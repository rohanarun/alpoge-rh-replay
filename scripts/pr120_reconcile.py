#!/usr/bin/env python3
"""Bind PR120 tracker rows to exact Git blobs; never infer that a change fixed Lean."""
import argparse
import json
import re
import subprocess
from pathlib import Path

BRANCH = "opt/collapse-and-consolidate-4.36"
REPO = "rohanarun/riemann-hypothesis"
HEAD_RE = re.compile(r"\bhead `([0-9a-f]{7,40})`")
ROW_RE = re.compile(r"^\| `([^:`]+\.lean):(\d+)(?::\d+)?`\s*\|")
CLAIM_RE = re.compile(r"\bclaimed:\s*#(\d+)")


def git(repo, *args):
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True
    ).stdout


def commit(repo, ref):
    return git(repo, "rev-parse", "--verify", "--end-of-options", ref + "^{commit}").decode().strip()


def lean_blobs(repo, sha):
    result = {}
    for record in git(repo, "ls-tree", "-r", "-z", sha, "--", "src").split(b"\0"):
        if not record:
            continue
        metadata, path = record.split(b"\t", 1)
        mode, kind, oid = metadata.split()
        if kind == b"blob" and mode in (b"100644", b"100755") and path.endswith(b".lean"):
            result[path.decode("utf-8")] = oid.decode()
    return result


def parse_tracker(text):
    head = HEAD_RE.search(text)
    if not head:
        raise ValueError("Could not read the tracker commit")
    count = None
    in_open = False
    rows = {}
    for line in text.splitlines():
        if line.startswith("## "):
            section = re.fullmatch(r"## Open \(([\d,]+)\)\s*", line)
            in_open = section is not None
            if section:
                count = int(section[1].replace(",", ""))
        if in_open and (m := ROW_RE.match(line)):
            rel = m[1] if m[1].startswith("src/") else "src/" + m[1]
            row = rows.setdefault(rel, {"lines": [], "tracker_prs": []})
            row["lines"].append(int(m[2]))
            row["tracker_prs"].extend(int(p) for p in CLAIM_RE.findall(line))
    if count is None or sum(len(row["lines"]) for row in rows.values()) != count:
        raise ValueError("Tracker open row count does not match parsed entries")
    return head[1], rows


def complete_pr_snapshot(snapshot):
    return bool(snapshot and snapshot.get("listing_complete") is True and not any(
        pr.get("errors") for pr in snapshot["pulls"]
    ))


def reconcile(rows, old, new, snapshot):
    overlaps = {}
    warnings = []
    if snapshot is None:
        warnings.append("No open-PR snapshot; overlaps are unknown.")
    else:
        if snapshot.get("base") != BRANCH or snapshot.get("repository") != REPO:
            raise ValueError("Open-PR snapshot is for the wrong repository or base branch")
        if snapshot.get("listing_complete") is not True:
            warnings.append("Open-PR listing completeness is not confirmed.")
        for pr in snapshot["pulls"]:
            if pr.get("errors"):
                warnings.append(f"Incomplete or changing file list for PR #{pr['number']}.")
            for path in pr["files"]:
                overlaps.setdefault(path, set()).add(pr["number"])
    complete = complete_pr_snapshot(snapshot)
    output = []
    for path, row in sorted(rows.items()):
        before, after = old.get(path), new.get(path)
        pr_numbers = sorted(overlaps.get(path, ()))
        if before is None:
            status = "missing-at-tracker-commit"
        elif after is None:
            status = "removed-since-tracker"
        elif before != after:
            status = "changed-recheck"
        elif pr_numbers:
            status = "unchanged-overlap"
        elif row["tracker_prs"]:
            status = "unchanged-tracker-claim"
        else:
            status = "unchanged-reproduce-first"
        output.append({
            "path": path, "status": status, "tracker_blob": before, "source_blob": after,
            "lines": row["lines"], "tracker_prs": sorted(set(row["tracker_prs"])),
            "open_pr_overlaps": pr_numbers if pr_numbers or complete else None,
        })
    warnings.append("No status establishes a successful build; unchanged roots may compile after other dependencies change.")
    return output, warnings


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("tracker", type=Path)
    parser.add_argument("--source-ref", default="HEAD")
    parser.add_argument("--open-prs", type=Path, help="Optional archived API file list; never contacted by this script")
    args = parser.parse_args()
    try:
        tracker_ref, rows = parse_tracker(args.tracker.read_text(encoding="utf-8"))
        tracker_head, source_head = commit(args.repo, tracker_ref), commit(args.repo, args.source_ref)
        snapshot = json.loads(args.open_prs.read_text(encoding="utf-8")) if args.open_prs else None
        result, warnings = reconcile(rows, lean_blobs(args.repo, tracker_head), lean_blobs(args.repo, source_head), snapshot)
        if tracker_head != source_head:
            warnings.insert(0, "Tracker and analysis commits differ; the error list may be stale.")
        print(json.dumps({
            "tracker_head": tracker_head, "source_head": source_head,
            "open_pr_snapshot_completed": snapshot.get("read_completed_at") if snapshot else None,
            "open_pr_overlap_complete": complete_pr_snapshot(snapshot),
            "warnings": warnings, "rows": result
        }, ensure_ascii=False, indent=2, sort_keys=True))
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()
