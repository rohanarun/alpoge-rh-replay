# Check a PR #120 failure before claiming it

The build report and branch advance independently. A row can still describe an
older version of a module, and the report's claim notes can lag open PRs.
This read-only helper compares the report with your local checkout and live PRs:

```sh
python3 scripts/pr120-triage.py --checkout /path/to/riemann-hypothesis
```

It reads the normal build's **Open** table. The separate look-ahead table can
combine scratch sessions at different commits, so it is excluded from this
comparison rather than being attributed to the normal build's head.

Run it from this replay repository after updating both repositories. It uses
Python's standard library, Git, and an authenticated `gh` CLI. The target checkout
should be on `opt/collapse-and-consolidate-4.36`, or a branch based on it. The tool
does not fetch, switch branches, build Lean, create claims, or modify either repository.

The source column distinguishes files changed since the report's build commit,
files unchanged since that commit, local edits, and paths absent from the current
Git tree. Sparse checkout exclusions are not treated as deleted files. If a
shallow checkout lacks the reported commit, the comparison is explicitly unknown;
fetch its full SHA or use a checkout containing that history.
An older or unrelated checkout also produces unknown comparisons instead of
presenting reversed differences as fixes made since the report.

The claim column reports PRs that currently change each module and retains claims
recorded in the report. A zero-file PR also reserves a module when its title is
exactly `Fix <full.dotted.module>`, following the project's early claim convention.
Partial titles and matching basenames in other directories are not inferred.
Larger PR file lists are fetched with pagination. If GitHub
still truncates a PR's file list or the PR list reaches
its limit, unmatched claims are unknown, rather than being called unclaimed.
GitHub/authentication failures exit with status 2 instead of implying no claims exist.

**Changed does not mean fixed; unchanged does not mean still broken.** Build the
module before claiming it, then follow [auto-research.md](../auto-research.md).
Even a complete claim snapshot can change after the tool finishes.

For agents or scripts, add `--json`. To inspect a saved report, add
`--report /path/to/PR120-BUGS.md`. For local comparisons without GitHub, add
`--offline`; claim status will remain unknown except for reported claims.

Run the offline regression suite with:

```sh
python3 -m unittest discover -s tests -p 'test_pr120_triage.py' -v
```
