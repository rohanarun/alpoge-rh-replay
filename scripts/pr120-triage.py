#!/usr/bin/env python3
"""Check PR120-BUGS.md against a local checkout and current GitHub claims.

This is a read-only preflight, not a Lean build or a determination that a bug is fixed.
See scripts/pr120-triage.md for usage and status definitions.
"""

import argparse
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


REPO = "rohanarun/riemann-hypothesis"
BASE = "opt/collapse-and-consolidate-4.36"
DEFAULT_REPORT = Path(__file__).resolve().parents[1] / "PR120-BUGS.md"


def run(args):
    result = subprocess.run(args, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip())
    return result.stdout


def parse_report(text):
    head = re.search(r"\bhead `([0-9a-f]{7,40})`", text)
    if not head:
        raise ValueError("Report has no build head SHA.")
    failures = []
    in_open = False
    for line in text.splitlines():
        if line.startswith("## "):
            in_open = bool(re.fullmatch(r"## Open \(\d+\)", line.strip()))
        if not in_open:
            continue
        row = re.match(r"\|\s*`([^`]+\.lean):(\d+)`\s*\|", line)
        if not row:
            continue
        module = PurePosixPath(row[1])
        if module.is_absolute() or ".." in module.parts:
            raise ValueError(f"Invalid module path: {module}")
        claims = re.findall(r"claimed:\s*#(\d+)", line)
        failures.append({"path": f"src/{module}", "line": int(row[2]),
                         "reported_claims": [int(n) for n in claims]})
    count = re.search(r"^## Open \((\d+)\)\s*$", text, re.M)
    if not count or len(failures) != int(count[1]):
        raise ValueError("Open failure count does not match recognized rows; check the report format.")
    return head[1], failures


def nul_paths(output):
    return set(output.rstrip("\0").split("\0")) if output else set()


def inspect_checkout(checkout, reported_head):
    prefix = ["git", "-C", str(checkout)]
    current = run(prefix + ["rev-parse", "--verify", "HEAD^{commit}"]).strip()
    tracked = nul_paths(run(prefix + ["ls-tree", "-r", "--name-only", "-z", "HEAD", "--", "src"]))
    # Include staged, unstaged, and untracked source edits without changing the checkout.
    local = nul_paths(run(prefix + ["diff", "--name-only", "-z", "HEAD", "--", "src"]))
    local |= nul_paths(run(prefix + ["ls-files", "--others", "--exclude-standard", "-z", "--", "src"]))
    try:
        run(prefix + ["rev-parse", "--verify", f"{reported_head}^{{commit}}"])
    except RuntimeError:
        warning = (f"Build commit {reported_head} is unavailable locally. Source comparisons are unknown; "
                   "fetch the report's full commit SHA or use a checkout containing its history.")
        return current, tracked, local, None, warning
    try:
        run(prefix + ["merge-base", "--is-ancestor", reported_head, current])
    except RuntimeError:
        warning = (f"Checkout HEAD is not a verified descendant of build commit {reported_head}. "
                   "Update the checkout/history before comparing; source comparisons are unknown.")
        return current, tracked, local, None, warning
    changed = nul_paths(run(prefix + ["diff", "--name-only", "-z", reported_head, current, "--", "src"]))
    warning = None
    return current, tracked, local, changed, warning


def index_claims(prs):
    claims = {}
    incomplete = []
    for pr in prs:
        files = pr["files"]
        if len(files) < pr["changedFiles"]:
            incomplete.append(pr["number"])
        for file in files:
            claims.setdefault(file["path"], []).append({"number": pr["number"], "url": pr["url"]})
    # The CLI request is bounded. Never silently interpret a truncated list as unclaimed.
    return claims, incomplete, len(prs) >= 1000


def fetch_claims():
    prs = json.loads(run(["gh", "pr", "list", "--repo", REPO, "--base", BASE,
                          "--limit", "1000", "--json", "number,url,files,changedFiles"]))
    for pr in prs:
        if len(pr["files"]) < pr["changedFiles"]:
            pages = json.loads(run(["gh", "api", "--paginate", "--slurp",
                                    f"repos/{REPO}/pulls/{pr['number']}/files?per_page=100"]))
            pr["files"] = [{"path": file["filename"]} for page in pages for file in page]
    return index_claims(prs)


def triage(failures, tracked, local, changed, claims, claims_complete):
    rows = []
    for failure in failures:
        path = failure["path"]
        if path in local:
            source = "local edits"
        elif path not in tracked:
            source = "absent at HEAD"
        elif changed is None:
            source = "unknown"
        elif path in changed:
            source = "changed since report"
        else:
            source = "unchanged since report"
        live = claims.get(path, [])
        claim_status = "claimed" if live else "unclaimed" if claims_complete else "unknown"
        if not live and failure["reported_claims"]:
            claim_status = "reported claim"
        rows.append(dict(failure, source=source, claim_status=claim_status, live_claims=live))
    return rows


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path, required=True, help="local riemann-hypothesis checkout")
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--offline", action="store_true", help="skip GitHub; unmatched claims remain unknown")
    parser.add_argument("--json", action="store_true", help="emit structured data, including warnings")
    args = parser.parse_args(argv)
    try:
        reported_head, failures = parse_report(args.report.read_text())
        current, tracked, local, changed, warning = inspect_checkout(args.checkout, reported_head)
        warnings = [warning] if warning else []
        claims, complete = {}, False
        if args.offline:
            warnings.append("GitHub claims were not checked (--offline).")
        else:
            claims, incomplete, truncated = fetch_claims()
            complete = not incomplete and not truncated
            if incomplete:
                warnings.append("GitHub omitted changed files for PRs " + ", ".join(f"#{n}" for n in incomplete)
                                + "; unmatched claims are unknown.")
            if truncated:
                warnings.append("Open PR list reached its limit; unmatched claims are unknown.")
        rows = triage(failures, tracked, local, changed, claims, complete)
        data = {"report_head": reported_head, "checkout_head": current, "warnings": warnings, "failures": rows}
    except (OSError, RuntimeError, ValueError, KeyError, TypeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(data, ensure_ascii=False, indent=2))
    else:
        print(f"Report {reported_head}; checkout {current[:12]}")
        for message in warnings:
            print(f"Warning: {message}")
        print("\nSource status\tClaim status\tModule (reported line)")
        for row in rows:
            ids = [f"#{p['number']}" for p in row["live_claims"]]
            ids += [f"report #{n}" for n in row["reported_claims"]]
            claim = row["claim_status"] + (f" ({', '.join(ids)})" if ids else "")
            print(f"{row['source']}\t{claim}\t{row['path']}:{row['line']}")
        print("\nChanged does not mean fixed; unchanged does not mean still broken. Compile before claiming.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
