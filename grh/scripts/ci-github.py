#!/usr/bin/env python3
"""Find the build of a commit whose cache outputs may be published, from GitHub's API.

usage: ci-github.py find-run --sha <commit> [--run-id N] [--wait-minutes M]
       ci-github.py queue-tested --sha <commit>

find-run prints (and writes to $GITHUB_OUTPUT) run_id and artifact for the run of
.github/workflows/build.yml in this repository that built <commit> on the self-hosted runner and
succeeded, and that has exactly one unexpired artifact named cache-<commit>. A merge_group run is
preferred: the merge queue fast-forwards main to the exact commit it tested. Otherwise a push or
workflow_dispatch run of <commit> is used, waiting up to --wait-minutes for one to appear and finish.
--run-id selects one run, which must pass the same checks.

queue-tested writes tested=true to $GITHUB_OUTPUT if a merge_group run of build.yml for <commit>
succeeded, so the push build of the same commit need not build it again.

Adapted from scripts/ci-github.py of branch alpoge. It reads GITHUB_REPOSITORY and GH_TOKEN.
"""
import argparse
import json
import os
import re
import sys
import time
import urllib.request

REPOSITORY = "leanprover-community/riemann-hypothesis"
WORKFLOW = ".github/workflows/build.yml"
JOB = "lake build"
LABEL = "rh-big"
SHA = re.compile(r"[0-9a-f]{40}\Z")


def api(path):
    request = urllib.request.Request(f"https://api.github.com/repos/{REPOSITORY}/{path}", headers={
        "Authorization": f"Bearer {os.environ['GH_TOKEN']}", "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "riemann-hypothesis-ci"})
    for attempt in range(5):
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                return json.load(response)
        except (OSError, ValueError):
            if attempt == 4:
                raise
            time.sleep(2 ** attempt)


def outputs(**values):
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a") as stream:
            for key, value in values.items():
                stream.write(f"{key}={value}\n")
    print(json.dumps(values, sort_keys=True), flush=True)


def runs(sha):
    return api(f"actions/workflows/build.yml/runs?head_sha={sha}&per_page=100").get("workflow_runs", [])


def event_problem(run):
    if run.get("event") not in ("merge_group", "push", "workflow_dispatch"):
        return f"event {run.get('event')}"
    if run.get("event") == "push" and run.get("head_branch") != "main":
        return f"a push to {run.get('head_branch')}"
    return None


def problem(run, sha):
    """Why this run's artifact must not be published, or None."""
    if (run.get("repository", {}).get("full_name") != REPOSITORY or run.get("path") != WORKFLOW
            or run.get("head_sha") != sha):
        return "not a build.yml run of this commit in this repository"
    if reason := event_problem(run):
        return reason
    if run.get("status") != "completed" or run.get("conclusion") != "success":
        return f"{run.get('status')} with conclusion {run.get('conclusion')}"
    jobs = api(f"actions/runs/{run['id']}/attempts/{run['run_attempt']}/jobs?per_page=100").get("jobs", [])
    build = [job for job in jobs if job.get("name") == JOB]
    if len(build) != 1 or build[0].get("conclusion") != "success" or LABEL not in build[0].get("labels", []):
        return f"no successful '{JOB}' job on the {LABEL} runner"
    return None


def artifact(run, sha):
    rows = api(f"actions/runs/{run['id']}/artifacts?per_page=100").get("artifacts", [])
    named = [row for row in rows if row.get("name") == f"cache-{sha}"]
    if len(named) != 1 or named[0].get("expired") is not False:
        return None
    return named[0]["name"]


def find_run(args):
    sha = args.sha
    if not SHA.fullmatch(sha):
        raise ValueError("--sha must be a full commit hash")
    deadline = time.monotonic() + 60 * args.wait_minutes
    while True:
        candidates = runs(sha)
        if args.run_id:
            candidates = [run for run in candidates if run.get("id") == args.run_id]
        else:
            candidates = [run for run in candidates if event_problem(run) is None]
        order = {"merge_group": 0, "push": 1, "workflow_dispatch": 2}
        candidates.sort(key=lambda run: (order.get(run.get("event"), 9), -run.get("id", 0)))
        # The publisher and the build both start on push. The build may not be listed yet.
        pending = not candidates
        for run in candidates:
            reason = problem(run, sha)
            if reason is None:
                name = artifact(run, sha)
                if name:
                    outputs(run_id=run["id"], artifact=name, event=run["event"])
                    return
                reason = f"no unexpired artifact cache-{sha}"
            print(f"run {run.get('id')} ({run.get('event')}): {reason}", flush=True)
            pending |= run.get("status") != "completed" and event_problem(run) is None
        remaining = deadline - time.monotonic()
        if not pending or remaining <= 0:
            raise ValueError(f"no successful self-hosted build of {sha} with a cache artifact")
        print("waiting for a build of this commit to appear or finish...", flush=True)
        time.sleep(min(30, remaining))


def queue_tested(args):
    tested = any(run.get("event") == "merge_group" and problem(run, args.sha) is None for run in runs(args.sha))
    outputs(tested=str(tested).lower())


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("find-run")
    command.add_argument("--sha", required=True)
    command.add_argument("--run-id", type=int)
    command.add_argument("--wait-minutes", type=int, default=0)
    command.set_defaults(function=find_run)
    command = commands.add_parser("queue-tested")
    command.add_argument("--sha", required=True)
    command.set_defaults(function=queue_tested)
    args = parser.parse_args()
    if os.environ.get("GITHUB_REPOSITORY", REPOSITORY) != REPOSITORY:
        raise ValueError("this script only serves leanprover-community/riemann-hypothesis")
    args.function(args)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError) as error:
        sys.exit(f"ci-github.py: {error}")
