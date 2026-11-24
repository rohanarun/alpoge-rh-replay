#!/usr/bin/env python3
"""Rank PR #120 tracker roots by static load-bearing impact (no Lean build)."""

from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import asdict, dataclass
import json
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys

HEADING = re.compile(r"^##\s+(.*)")
OPEN = re.compile(r"Open(?:\s*\(([\d,]+)\))?\s*$", re.I)
CHANGED = re.compile(r"Changed since this error\b", re.I)
LOCATION = re.compile(r"^\s*\|\s*`([^`]+?\.lean)(?::(\d+)(?::\d+)?)?`\s*\|")
REVISION = re.compile(r"\bhead\s+`([a-fA-F0-9]{7,64})`", re.I)
UPDATED = re.compile(r"\bUpdated\s+([^.\n]+)\.")
NAME_RE = re.compile(r"(?:[^\W\d]|_)[\w'!?₀-₉′]*|«[^»\r\n]+»|\.", re.UNICODE)
TO_COMMENT = re.compile(r"/-|-/")


@dataclass(frozen=True)
class Row:
    module: str
    path: str
    line: int | None
    category: str
    notes: str
    tracker_status: str

    @property
    def active(self):
        return self.tracker_status.startswith("open_")


def module_name(target):
    target = target.strip().replace("\\", "/")
    if target.startswith("./"):
        target = target[2:]
    if target.startswith("src/"):
        target = target[4:]
    if target.endswith(".lean"):
        target = target[:-5]
    return target.replace("/", ".")


def tracker_rows(markdown):
    rows = {}
    warnings = []
    section, declared, saw_open = None, None, False
    fenced = False
    for line in markdown.splitlines():
        if line.lstrip().startswith("```"):
            fenced = not fenced
        if fenced:
            continue
        if heading := HEADING.match(line):
            name = heading[1].strip()
            if opened := OPEN.fullmatch(name):
                section, saw_open = "open", True
                if opened[1]:
                    declared = int(opened[1].replace(",", ""))
            elif CHANGED.match(name):
                section = "changed"
            else:
                section = None
        if section is None or not (loc := LOCATION.match(line)):
            continue
        fields = [f.strip() for f in re.split(r"(?<!\\)\|", line[loc.end():])]
        category = fields[0]
        notes = fields[-2] if len(fields) >= 4 else ""
        module = module_name(loc[1])
        if section == "changed":
            status = "changed_rebuilding"
        elif re.search(r"\bclaimed\s*:", notes, re.I):
            status = "open_claimed"
        elif re.search(r"\bfix(?:\s+already)?\s+exists\b", notes, re.I):
            status = "open_fix_exists"
        else:
            status = "open_unclaimed"
        row = Row(module, loc[1], int(loc[2]) if loc[2] else None, category, notes, status)
        if module in rows:
            warnings.append(f"Duplicate tracker row for {module}; preferring an Open row.")
            if rows[module].active:
                continue
        rows[module] = row
    if not saw_open:
        warnings.append("No Open heading found; the active-root set is unknown.")
    elif declared is not None:
        actual = sum(row.active for row in rows.values())
        if actual != declared:
            warnings.append(f"Open heading says {declared}; parsed {actual} distinct active roots.")
    rev = REVISION.search(markdown)
    date = UPDATED.search(markdown)
    return rows, rev[1].lower() if rev else None, date[1] if date else None, warnings


def header_tokens(source):
    """Yield identifier/dot tokens only until the first non-header syntax."""
    pos = 1 if source.startswith("\ufeff") else 0
    while pos < len(source):
        if source[pos].isspace():
            pos += 1
        elif source.startswith("--", pos):
            end = source.find("\n", pos)
            pos = len(source) if end < 0 else end + 1
        elif source.startswith("/-", pos):
            depth, pos = 1, pos + 2
            while depth:
                match = TO_COMMENT.search(source, pos)
                if not match:
                    raise ValueError("unterminated Lean block comment in header")
                depth += 1 if match[0] == "/-" else -1
                pos = match.end()
        elif match := NAME_RE.match(source, pos):
            yield match[0]
            pos = match.end()
        else:
            return


def header_imports(source):
    """Read common Lean 4 header grammar, without scanning declarations."""
    tokens = iter(header_tokens(source))
    word = next(tokens, None)
    if word == "module":
        word = next(tokens, None)
    if word == "prelude":
        word = next(tokens, None)
    while word:
        while word in {"public", "private", "meta"}:
            word = next(tokens, None)
        if word != "import":
            break
        word = next(tokens, None)
        if word == "all":
            word = next(tokens, None)
        if not word or word == ".":
            raise ValueError("import missing module name in Lean header")
        parts = []
        while True:
            parts.append(word[1:-1] if word.startswith("«") else word)
            word = next(tokens, None)
            if word != ".":
                break
            word = next(tokens, None)
            if not word or word == ".":
                raise ValueError("invalid dotted name in Lean header")
        yield ".".join(parts)


def scan_graph(root, committed=None, algorithm="sha1"):
    paths = {}
    for folder, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and not (Path(folder) / d).is_symlink())
        for file in sorted(files):
            path = Path(folder) / file
            if not file.endswith(".lean") or path.is_symlink():
                continue
            module = module_name(path.relative_to(root).as_posix())
            if module in paths:
                raise ValueError(f"module path collision: {paths[module]} and {path}")
            paths[module] = path
    if not paths:
        raise ValueError("no Lean files found: pass the consolidated checkout or its src directory")
    reverse = {module: [] for module in paths}
    edges = 0
    seen_paths = set()
    dirty = 0
    for module, path in paths.items():
        try:
            raw = path.read_bytes()
            if committed is not None:
                relative = path.relative_to(root).as_posix()
                seen_paths.add(relative)
                digest = hashlib.new(algorithm, f"blob {len(raw)}\0".encode("ascii"))
                digest.update(raw)
                dirty += committed.get(relative) != digest.hexdigest()
            for dependency in set(header_imports(raw.decode("utf-8"))):
                if dependency in paths:
                    reverse[dependency].append(module)
                    edges += 1
        except ValueError as exc:
            raise ValueError(f"{path.relative_to(root)}: {exc}") from exc
    if committed is not None:
        dirty += len(committed.keys() - seen_paths)
    return reverse, edges, dirty


def count_impacts(reverse, roots):
    """Propagate active-root bitsets through downstream imports, including cycles."""
    roots = list(sorted(roots))
    bits = [1 << i for i in range(len(roots))]
    owners = dict.fromkeys(reverse, 0)
    pending = deque(root for root in roots if root in reverse)
    queued = set(pending)
    for root, bit in zip(roots, bits):
        if root in reverse:
            owners[root] = bit
    while pending:
        current = pending.popleft()
        queued.remove(current)
        mask = owners[current]
        for dependent in reverse[current]:
            merged = owners[dependent] | mask
            if merged != owners[dependent]:
                owners[dependent] = merged
                if dependent not in queued:
                    queued.add(dependent)
                    pending.append(dependent)
    histogram = Counter(owners.values())
    totals = Counter()
    for mask, count in histogram.items():
        while mask:
            bit = mask & -mask
            totals[bit] += count
            mask ^= bit
    return {
        root: (totals[bit] - 1, histogram[bit] - (owners[root] == bit)) if root in reverse else (None, None)
        for root, bit in zip(roots, bits)
    }, len(owners) - histogram[0]


def git_checkout_root(root):
    root = root.resolve()
    if root.name == "src" and (root.parent / ".git").exists():
        root = root.parent
    return root if (root / ".git").exists() else None


def git_revision(root):
    # rev-parse reads revision metadata; it does not run project hooks or code.
    if root is None:
        return None
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--verify", "HEAD^{commit}"],
            check=True, capture_output=True, text=True, timeout=5,
        )
        sha = result.stdout.strip().lower()
        return sha if re.fullmatch("(?:[a-f0-9]{40}|[a-f0-9]{64})", sha) else None
    except (OSError, subprocess.SubprocessError):
        return None


def git_lean_blobs(checkout, source, sha):
    """Read only committed tree metadata; do not run Git worktree filters."""
    relative = source.resolve().relative_to(checkout).as_posix()
    prefix = relative + "/" if relative != "." else ""
    try:
        result = subprocess.run(
            ["git", "-C", str(checkout), "ls-tree", "-r", "-z", "--full-tree", sha,
             "--", relative], check=True, capture_output=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    blobs = {}
    for entry in result.stdout.split(b"\0"):
        if not entry:
            continue
        metadata, raw_path = entry.split(b"\t", 1)
        mode, kind, blob = metadata.split()
        path = os.fsdecode(raw_path)
        if mode in {b"100644", b"100755"} and kind == b"blob" and path.endswith(".lean"):
            if path.startswith(prefix) and not any(part.startswith(".") for part in path[len(prefix):].split("/")[:-1]):
                blobs[path[len(prefix):]] = blob.decode("ascii")
    return blobs


def make_report(source, markdown, targets=(), source_revision=None):
    project_root = source / "src" if (source / "src").is_dir() else source
    rows, tracker_rev, updated, warnings = tracker_rows(markdown)
    checkout = git_checkout_root(source)
    actual_rev = git_revision(checkout)
    if source_revision and actual_rev and not actual_rev.startswith(source_revision):
        warnings.append(f"Supplied source revision {source_revision} disagrees with checkout HEAD {actual_rev}; using HEAD.")
    source_rev = actual_rev or source_revision
    if not source_rev or not tracker_rev:
        revision_status = "unverified"
        warnings.append("Cannot compare revisions: missing source checkout HEAD or tracker head.")
    elif not (source_rev.startswith(tracker_rev) or tracker_rev.startswith(source_rev)):
        revision_status = "skew"
        warnings.append(f"Revision skew: source {source_rev} vs tracker {tracker_rev}; treat statuses and counts as provisional.")
    else:
        revision_status = "match"
    committed = git_lean_blobs(checkout, project_root, actual_rev) if actual_rev else None
    reverse, edges, dirty = scan_graph(project_root, committed, "sha256" if actual_rev and len(actual_rev) == 64 else "sha1")
    if dirty:
        warnings.append(f"Dirty source tree: {dirty} Lean file(s) differ from HEAD or are untracked; counts reflect worktree files.")
    elif actual_rev and committed is None:
        warnings.append("Could not verify whether Lean source files match checkout HEAD.")
    active = {module for module, row in rows.items() if row.active}
    counts, union_inclusive = count_impacts(reverse, active)
    missing = sorted(active - reverse.keys())
    if missing:
        warnings.append(f"{len(missing)} active tracker roots are missing from the source tree; overlapping/exclusive counts may be incomplete.")

    def record(module):
        row = rows.get(module)
        present = module in reverse
        total, exclusive = counts.get(module, (None, None))
        return dict(
            asdict(row) if row else dict(module=module, path=None, line=None, category=None, notes="",
                                         tracker_status="not_listed"),
            source_present=present,
            affected_downstream=total,
            exclusive_affected_downstream=exclusive,
        )

    listed = sorted((record(module) for module in active), key=lambda r: (
        r["affected_downstream"] is None,
        -(r["exclusive_affected_downstream"] or 0),
        -(r["affected_downstream"] or 0), r["module"],
    ))
    return {
        "schema_version": 1, "source_revision": source_rev, "tracker_revision": tracker_rev,
        "revision_status": revision_status, "tracker_updated": updated, "source_modules": len(reverse),
        "source_lean_file_differences_from_head": dirty if committed is not None else None,
        "source_import_edges": edges, "active_tracker_roots": len(active),
        "reachable_modules_including_active_roots": union_inclusive, "missing_active_roots": missing,
        "warnings": warnings, "roots": listed,
        "targets": [record(module) for module in dict.fromkeys(map(module_name, targets))],
    }


def display_table(report):
    lines = [
        f"Source {report['source_revision'] or 'unknown'} | tracker {report['tracker_revision'] or 'unknown'} | {report['revision_status']}",
        f"{report['source_modules']} modules, {report['source_import_edges']} project imports, {report['active_tracker_roots']} active roots",
        "Exclusive | Downstream | Tracker status | In source | Module",
    ]
    for title, records in (("Active roots", report["roots"]), ("Requested targets", report["targets"])):
        if not records:
            continue
        lines.append(f"[{title}]")
        for row in records:
            ex, all_ = row["exclusive_affected_downstream"], row["affected_downstream"]
            lines.append(
                f"{ex if ex is not None else '-':>9} | {all_ if all_ is not None else '-':>10} | "
                f"{row['tracker_status']} | {'yes' if row['source_present'] else 'no'} | {row['module']}"
            )
    return "\n".join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source", type=Path, help="checkout root or src/")
    p.add_argument("tracker", type=Path, help="PR120-BUGS.md file")
    p.add_argument("--target", action="append", default=[], help="module or .lean path (repeatable)")
    p.add_argument("--format", choices=("table", "json"), default="table")
    p.add_argument("--source-revision", type=lambda sha: sha.lower(), help="declared commit ID for a source archive")
    args = p.parse_args()
    if args.source_revision and not re.fullmatch(r"[a-f0-9]{7,64}", args.source_revision):
        p.error("--source-revision must be a hexadecimal Git commit ID")
    try:
        report = make_report(args.source, args.tracker.read_text(encoding="utf-8"), args.target, args.source_revision)
    except (OSError, ValueError) as exc:
        p.exit(2, f"error: {exc}\n")
    if args.format == "json":
        print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        for warning in report["warnings"]:
            print(f"WARNING: {warning}", file=sys.stderr)
        print(display_table(report))


if __name__ == "__main__":
    main()
