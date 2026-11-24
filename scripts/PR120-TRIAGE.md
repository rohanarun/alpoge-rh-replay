# PR #120 static dependency triage

Run with Python 3.10+ (standard library only; optional Git for HEAD comparison).
Use the consolidated PR #120 branch source, not the replay repository's original
module index. The tracker is the replay repository's `PR120-BUGS.md`.

```sh
python scripts/pr120_triage.py path/to/consolidated-checkout path/to/PR120-BUGS.md
python scripts/pr120_triage.py path/to/consolidated-checkout/src path/to/PR120-BUGS.md \
  --format json \
  --target Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneNotMemFilOne \
  --target Development/AbelianVarietyTheory/Proofs/DivisorProofs/Bundle0715.lean
python -m unittest discover -s scripts -p 'test_pr120_triage.py' -v
```

For an archive with no Git metadata, optionally pass its provenance as
`--source-revision COMMIT`. That label is caller-supplied, not verified against
the archive's contents. Otherwise the report compares the tracker head to the
checkout HEAD. It checks the worktree’s analyzed Lean files against the
committed Git blob IDs, including modified, missing, and untracked Lean files.
The tool reads files and invokes only Git metadata lookup (if available). It does not run Lean/Lake, edit the inputs, fetch the network, or
look up live claims.

## Output interpretation

- **Downstream** is the count of distinct source modules that directly or
  transitively import an active tracker root, excluding the root itself.
- **Exclusive** counts downstream modules whose set of active tracker roots
  in the transitive, reflexive import closure is exactly that root. A listed
  root contributes its own bit when propagated through a chain; it is not
  included in its own downstream counts. Exclusive rows cannot overlap.
- **Active** means in the tracker's Open table, including claimed roots and
  those with a reference fix. A separate changed/rebuilding section does not
  contribute roots. The report distinguishes `open_unclaimed`, `open_claimed`,
  `open_fix_exists`, `changed_rebuilding`, and `not_listed`; a claim takes
  precedence over a reference fix in the status label (original notes remain).
  Source presence is an independent field.
- **Not listed** does not mean fixed, clean or available. A missing root has
  unknown (not zero) impact; missing roots also make other counts provisional.
  A zero exclusive count can still mean a fix is needed to unblock a cluster.
- Counts measure static reachability within the supplied tree. They are not
  current failures, actual successful rebuilds, or guarantees that a fix
  unblocks anything. Other failures can emerge, changed modules can still be
  rebuilding, and external-package imports do not create nodes.
- A revision mismatch warns rather than silently joining a fresh tracker to a
  different graph. Independently check current claims and fixes before acting.

## Reconcile a tracker snapshot with a newer commit

```sh
python scripts/pr120_reconcile.py path/to/consolidated-checkout PR120-BUGS.md \
  --source-ref NEW_COMMIT
python -m unittest discover -s scripts -p 'test_pr120_*.py' -v
```

The checkout must contain both the tracker commit and the newer commit.
Reconciliation compares Git blobs, not working-tree files. A changed blob
means recheck, not repaired; an unchanged blob may already work because a
dependency changed or because a shard diagnostic is from an earlier run.

Optionally supply `--open-prs snapshot.json`, a previously collected public
snapshot with `repository`, `base`, `read_completed_at`, `listing_complete`, and `pulls`. The
expected repository is `rohanarun/riemann-hypothesis` and the expected base
is `opt/collapse-and-consolidate-4.36`. Each item in `pulls` has an integer
`number`, a list of repo-relative `files`, and an optional `errors` list.
Set `listing_complete` only if all open PRs and their full file lists
were verified. Otherwise rows without a known overlap return null.
Lack of overlap does not confirm availability. The reconciliation CLI does not perform any network calls.

## Reproduced example

For the [03:06 UTC tracker snapshot](https://github.com/rohanarun/alpoge-rh-replay/blob/438a87583f2106f17bbb451085c49b8ea5dffe47/PR120-BUGS.md),
use source commit `1c5f0accc9a1e44d4166867f5452c8bc68440979` for the matching graph.
It contains 47,885 project modules, 494,937 internal import edges, and 35
reported roots. For example, `DivisorProofs.Bundle0715` has 18,209 downstream
modules; 318 are exclusive to that root among the 35 reported roots. The
reconcile command, comparing that commit to
`6a422b6b5c71803f50a534fe4a14c2a38d7e99f4`, reports source edits in 10 of
the 35 root files. This is a historical example, not a current claim list.
