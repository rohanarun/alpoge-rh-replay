#!/usr/bin/env python3
"""Verify a build's staged cache outputs for one commit, and publish them to the shared cache.

usage: publish-ci-cache.py --sha <commit> --staging <dir> [--project DIR] [--publish]

Run by .github/workflows/publish-ci-cache.yml on a GitHub-hosted runner, from main's checkout:
the code here and in scripts/ci-cache-get.py is trusted, the staging directory is not. It was
written by scripts/ci-cache-stage.py in a build of <commit> on the self-hosted runner, and
downloaded from that run's artifact. Nothing from the staging directory or from <commit> is
executed: the build inputs of <commit> are read from Git objects only.

Checks, before any credential is read:
- the staging directory holds exactly outputs.jsonl, modules.jsonl.gz and artifacts/, with
  regular files only;
- the record for <commit> is computed here, from the Git objects of <commit> and the SHA-256 of
  the map and module manifest, and the map and manifest pass the checks of
  scripts/ci-cache-get.py for these build inputs (the manifest's header is bound to the inputs
  and to the map, and the manifest covers the map exactly);
- the manifest's modules are exactly the source files under src at <commit>;
- every staged artifact is named in the manifest and has the manifest's SHA-256; every other
  artifact of the manifest is downloaded from the public cache and checked the same way;
- every artifact's name is its stock Lake content hash (computeBinFileHash, with the toolchain of
  <commit>), and stock leantar extracts it.

With --publish, it then derives the R2 key from R2_ACCOUNT_TOKEN and writes, each with
If-None-Match (nothing is ever overwritten): the new artifacts, the map, the module manifest and
last the record, grh-lean/grh/inputs/<input fingerprint>.json. If a successful record for the
same build inputs is already published (from another commit with the same inputs), it writes
nothing at all. An existing object with other bytes is an error, except for the record. Adapted from scripts/publish-ci-cache.py of branch alpoge and from
the hand publisher of the rh-buildq hosts.

The cache does not verify any proof. As on every build host, the build itself is trusted to
have produced these artifacts for these input hashes: that cannot be checked without building.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request

spec = importlib.util.spec_from_file_location("ci_cache_get", Path(__file__).with_name("ci-cache-get.py"))
cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cli)

FETCH_ARTIFACTS = Path(__file__).with_name("fetch-artifacts.py")
ACCOUNT = "ec2169bdf033f56b009956d4b64ba8ef"
BUCKET = "riemann-hypothesis-cache"
S3 = f"https://{ACCOUNT}.r2.cloudflarestorage.com/{BUCKET}/"
ARTIFACT_TYPE = "application/vnd.reservoir.artifact"
MAP_TYPE = "application/vnd.reservoir.outputs+json-lines"
IMMUTABLE = "public, max-age=31536000, immutable"
ARTIFACT_PREFIX = f"artifacts/{cli.SCOPE}/"
TOOLCHAIN = re.compile(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?\Z")
MAX_ARTIFACT = 1 << 30
MAX_METADATA = 64 << 20
WORKERS = 32

HASH_SOURCE = '''import Lake.Build.Trace
import Lean.Data.Json.FromToJson
open Lake Lean
def main (args : List String) : IO Unit := do
  let [jobs, output] := args | throw <| IO.userError "expected jobs and output"
  let input ← IO.FS.Handle.mk jobs .read
  let out ← IO.FS.Handle.mk output .write
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let .ok job := Json.parse line | throw <| IO.userError "invalid job"
    let .ok file := job.getObjValAs? String "file" | throw <| IO.userError "missing file"
    let actual := (← computeBinFileHash file).toString
    out.putStrLn (Json.mkObj [("file", toJson file), ("actual", toJson actual)]).compress
  out.flush
'''


def log(message):
    print(f"{time.strftime('%H:%M:%S', time.gmtime())} {message}", flush=True)


def regular(path, maximum):
    """The bytes of an ordinary file, without following a symlink."""
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as handle:
        info = os.fstat(handle.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > maximum:
            raise ValueError(f"expected a bounded regular file: {path}")
        return handle.read(maximum + 1)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def source_modules(root, tree):
    paths = cli.source_paths(root, tree)
    if not paths or not all(path.endswith(".lean") for path in paths):
        raise ValueError("src must hold Lean files only")
    names = {path[:-5].replace("/", ".") for path in paths}
    if not all(cli.MODULE.fullmatch(name) for name in names):
        raise ValueError("unexpected module name under src")
    return names


def toolchain_prefix(toolchain):
    if not TOOLCHAIN.fullmatch(toolchain):
        raise ValueError(f"unexpected toolchain {toolchain!r}")
    prefix = Path(subprocess.check_output(["elan", "run", toolchain, "lean", "--print-prefix"], text=True).strip())
    if not (prefix / "bin/lean").is_file() or not (prefix / "bin/leantar").is_file():
        raise ValueError(f"no lean and leantar in {prefix}")
    return prefix


def lake_hashes(prefix, paths, work):
    """Stock Lake's content hash of each file, by computeBinFileHash with the stock toolchain."""
    source, jobs, output = work / "Hash.lean", work / "hash-jobs.jsonl", work / "hashes.jsonl"
    source.write_text(HASH_SOURCE)
    jobs.write_text("".join(json.dumps({"file": str(path)}) + "\n" for path in paths))
    library = prefix / "lib/lean/libLake_shared.so"
    subprocess.run([str(prefix / "bin/lean"), f"--load-dynlib={library}", "--run", str(source), str(jobs),
                    str(output)], cwd=work, check=True)
    return {row["file"]: row["actual"] for row in map(json.loads, output.read_text().splitlines())}


def extraction_error(prefix, archive, work):
    """None if stock leantar extracts the archive into a scratch directory, else the error."""
    target = Path(tempfile.mkdtemp(prefix="ltar-check-", dir=work))
    try:
        job = [{"file": str(archive), "hash": "0", "base": [str(target / part) for part in "abcd"]}]
        result = subprocess.run([str(prefix / "bin/leantar"), "-x", "-j", "-"], input=json.dumps(job).encode(),
                                capture_output=True, timeout=600)
        output = (result.stdout + result.stderr).decode(errors="replace").strip()
        if result.returncode or "corrupt" in output:
            return f"leantar exit {result.returncode}: {output[:200]}"
        return None
    finally:
        shutil.rmtree(target, ignore_errors=True)


def verify(root, sha, staging, work):
    """Check everything; return what to publish. Reads no credential."""
    if not re.fullmatch(r"[0-9a-f]{40}", sha) or git(root, "cat-file", "-t", sha) != "commit":
        raise ValueError(f"{sha} is not a commit of this checkout")
    identity = cli.identity_at(root, sha, {})
    prefix = toolchain_prefix(identity["toolchain"])
    names = source_modules(root, identity["source_tree"])
    if staging.is_symlink() or not staging.is_dir() or {path.name for path in staging.iterdir()} != {
            "outputs.jsonl", "modules.jsonl.gz", "artifacts"}:
        raise ValueError("the staging directory must hold exactly outputs.jsonl, modules.jsonl.gz and artifacts/")
    staged_dir = staging / "artifacts"
    if staged_dir.is_symlink() or not staged_dir.is_dir():
        raise ValueError("artifacts/ must be a directory")
    contents = regular(staging / "outputs.jsonl", MAX_METADATA)
    manifest = regular(staging / "modules.jsonl.gz", MAX_METADATA)
    fingerprint = cli.fingerprint(identity)
    map_sha, manifest_sha = cli.digest(contents), cli.digest(manifest)
    record = {"schema": 1, "repository": cli.REPOSITORY, "project": cli.PROJECT, **identity,
              "candidate_head": sha, "candidate_tree": git(root, "rev-parse", f"{sha}^{{tree}}"),
              "input_fingerprint": fingerprint, "build_exit_code": 0,
              "map_key": f"{cli.PREFIX}/maps/{map_sha}.jsonl", "map_sha256": map_sha,
              "module_manifest_key": f"{cli.PREFIX}/module-manifests/{manifest_sha}.jsonl.gz",
              "module_manifest_sha256": manifest_sha, "module_manifest_bytes": len(manifest)}
    record_bytes = (json.dumps(record, sort_keys=True, indent=1) + "\n").encode()
    if cli.matching_record(record_bytes, identity) != record:
        raise ValueError("the computed record does not pass scripts/ci-cache-get.py's checks")
    blobs = {record["map_key"]: contents, record["module_manifest_key"]: manifest}
    _, shas, modules = cli.validated_blobs(record, identity, lambda key, maximum: blobs[key])
    listed = {name for name, _, _ in modules}
    if listed != names:
        raise ValueError(f"the manifest's modules differ from src at {sha}: "
                         f"{len(listed - names)} not in src, {len(names - listed)} missing")
    staged = {}
    for path in staged_dir.iterdir():
        if path.name not in shas:
            raise ValueError(f"staged artifact {path.name} is not in the manifest")
        data = regular(path, MAX_ARTIFACT)
        if cli.digest(data) != shas[path.name]:
            raise ValueError(f"staged artifact {path.name} does not have the manifest's SHA-256")
        staged[path.name] = path
    log(f"{len(modules)} modules, {len(shas)} artifacts, {len(staged)} staged; fetching the others")
    others = {artifact: sha256 for artifact, sha256 in shas.items() if artifact not in staged}
    cache = work / "public"
    (cache / "artifacts").mkdir(parents=True)
    if others:
        fetch_map = work / "others.jsonl"
        fetch_map.write_text(json.dumps(cli.SCHEMA) + "\n" + "".join(
            json.dumps([artifact[:16], artifact]) + "\n" for artifact in sorted(others)))
        (work / "others-sha256.json").write_text(json.dumps(others))
        result = subprocess.run([sys.executable, "-I", str(FETCH_ARTIFACTS), str(fetch_map), str(cache),
                                 "--sha256", str(work / "others-sha256.json"),
                                 "--base-url", f"{cli.PUBLIC_BASE}/{ARTIFACT_PREFIX}"])
        if result.returncode:
            missing = [artifact for artifact in others if not (cache / "artifacts" / artifact).is_file()]
            raise ValueError(f"{len(missing)} artifacts are neither staged nor in the public cache with the"
                             f" manifest's SHA-256, for example {missing[:5]}")
    paths = {**{artifact: cache / "artifacts" / artifact for artifact in others}, **staged}
    log(f"checking the Lake content hash and test extraction of {len(paths)} artifacts")
    hashes = lake_hashes(prefix, list(paths.values()), work)
    wrong = [artifact for artifact, path in paths.items() if hashes.get(str(path)) != artifact[:16]]
    if wrong:
        raise ValueError(f"{len(wrong)} artifacts are not named by their Lake content hash, for example {wrong[:5]}")
    with ThreadPoolExecutor(WORKERS) as pool:
        errors = [(artifact, error) for artifact, error in zip(
            paths, pool.map(lambda path: extraction_error(prefix, path, work), paths.values())) if error]
    if errors:
        raise ValueError(f"{len(errors)} artifacts fail test extraction, for example {errors[:3]}")
    log(f"verified: record for {sha}, input fingerprint {fingerprint}")
    return {"identity": identity, "record": record, "record_bytes": record_bytes, "contents": contents,
            "manifest": manifest, "staged": staged, "shas": shas}


def credentials():
    """R2's S3 key from the Cloudflare account API token in R2_ACCOUNT_TOKEN, as on branch alpoge."""
    token = os.environ.pop("R2_ACCOUNT_TOKEN", "")
    if not token or any(character.isspace() for character in token):
        raise ValueError("publishing needs the R2_ACCOUNT_TOKEN secret of the ci-cache-publish environment")
    request = urllib.request.Request(f"https://api.cloudflare.com/client/v4/accounts/{ACCOUNT}/tokens/verify",
                                     headers={"Authorization": f"Bearer {token}"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            result = json.load(response)
    except urllib.error.HTTPError as error:
        raise ValueError(f"the account API token was refused (HTTP {error.code})") from None
    if not result.get("success") or result.get("result", {}).get("status") != "active":
        raise ValueError("the account API token is not active")
    access = result["result"]["id"]
    if not isinstance(access, str) or not re.fullmatch(r"[A-Za-z0-9]{16,128}", access):
        raise ValueError("unexpected token id")
    return access, hashlib.sha256(token.encode()).hexdigest()


class R2:
    """S3 requests to R2 with curl; the key stays in a private curl config file, not in argv."""

    def __init__(self, temporary):
        access, secret = credentials()
        self.config = Path(temporary) / "curl-auth.conf"
        descriptor = os.open(self.config, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(descriptor, "w") as handle:
            handle.write(f'user = "{access}:{secret}"\naws-sigv4 = "aws:amz:auto:s3"\n')

    def _curl(self, args, body=None):
        result = subprocess.run(["curl", "--disable", "-sS", "-K", str(self.config), "-o", "-", "-w", "\n%{http_code}",
                                 "--retry", "3", "--retry-all-errors", "--max-time", "300", *args],
                                input=body, capture_output=True)
        data, _, code = result.stdout.rpartition(b"\n")
        return int(code or 0), data

    def get(self, key):
        code, data = self._curl([S3 + key])
        if code == 404:
            return None
        if code != 200:
            raise RuntimeError(f"GET {key}: HTTP {code}")
        return data

    def create(self, key, data, content_type, cache_control, metadata=None):
        """PUT with If-None-Match: *. True if created, False if the key already exists."""
        args = ["-X", "PUT", "-H", "Content-Type: " + content_type, "-H", "Cache-Control: " + cache_control,
                "-H", "If-None-Match: *", "--data-binary", "@-"]
        for name, value in (metadata or {}).items():
            args += ["-H", f"x-amz-meta-{name}: {value}"]
        code, output = self._curl([*args, S3 + key], data)
        if code in (200, 201):
            return True
        if code == 412:
            return False
        raise RuntimeError(f"PUT {key}: HTTP {code} {output[:200]!r}")

    def immutable(self, key, data, content_type, metadata=None):
        if self.create(key, data, content_type, IMMUTABLE, metadata):
            return "created"
        if self.get(key) != data:
            raise ValueError(f"an existing object has other bytes, left unchanged: {key}")
        return "already present"


def publish(checked):
    record, identity = checked["record"], checked["identity"]
    with tempfile.TemporaryDirectory(prefix="publish-ci-cache-auth-") as temporary:
        r2 = R2(temporary)
        key = f"{cli.PREFIX}/inputs/{record['input_fingerprint']}.json"
        existing = r2.get(key)
        if existing is not None and existing != checked["record_bytes"] and cli.matching_record(existing, identity):
            # Another commit with the same build inputs was published first (by hand, or an
            # earlier build): its map and artifacts serve this commit, so write nothing.
            log(f"record {key}: a successful record for these build inputs (from"
                f" {json.loads(existing).get('candidate_head')}) is already published; nothing to write")
            return

        def upload(item):
            artifact, path = item
            return r2.immutable(ARTIFACT_PREFIX + artifact[:16] + ".art", regular(path, MAX_ARTIFACT),
                                ARTIFACT_TYPE, {"sha256": checked["shas"][artifact]})

        with ThreadPoolExecutor(WORKERS) as pool:
            results = list(pool.map(upload, sorted(checked["staged"].items())))
        log(f"artifacts: {results.count('created')} created, {results.count('already present')} already present")
        log(f"map {record['map_key']}: " + r2.immutable(record["map_key"], checked["contents"], MAP_TYPE))
        log(f"module manifest {record['module_manifest_key']}: "
            + r2.immutable(record["module_manifest_key"], checked["manifest"], "application/gzip"))
        if r2.create(key, checked["record_bytes"], "application/json", "no-cache"):
            log(f"record {key}: created")
        else:
            existing = r2.get(key)
            if existing == checked["record_bytes"]:
                log(f"record {key}: already present")
            elif existing is not None and cli.matching_record(existing, identity) is not None:
                log(f"record {key}: a successful record for these build inputs (from"
                    f" {json.loads(existing).get('candidate_head')}) is already published; left unchanged")
            else:
                raise ValueError(f"an existing record with other contents is not valid for these inputs: {key}")
    for attempt in range(6):
        if cli.find_record(identity) is not None:
            log("the public endpoint serves a valid record for these build inputs")
            return
        time.sleep(2 ** attempt)
    raise ValueError("the public endpoint does not serve the record")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sha", required=True)
    parser.add_argument("--staging", type=Path, required=True)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--publish", action="store_true", help="publish after verifying (needs R2_ACCOUNT_TOKEN)")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="publish-ci-cache-") as work:
        checked = verify(args.project.resolve(), args.sha, args.staging, Path(work))
        if args.publish:
            publish(checked)
        else:
            os.environ.pop("R2_ACCOUNT_TOKEN", None)
            log("verified only (no --publish)")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, RuntimeError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"CI cache publication refused: {error}")
