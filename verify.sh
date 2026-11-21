#!/usr/bin/env bash
set -euo pipefail
record="$(cd "$(dirname "$0")" && pwd -P)"
work="${1:?Supply an existing data directory path (e.g. /mnt/data2/rhv)}"
work="$(cd "$work" && pwd -P)"
exec > >(tee "$work/replay.log") 2>&1
export XDG_CACHE_HOME="$work/cache"
mkdir -p "$work"
cd "$work/parts"
while read -r hash part; do
  if [[ -f "$part" ]]; then continue; fi
  curl --fail --location --retry 4 --output "$part" "https://alpo.ge/lean.tar.gz.$part"
done < "$record/parts.sha256"
sha256sum -c "$record/parts.sha256"
if [[ ! -d "$work/lean/src" ]]; then
  cat part* | tar -xz --no-same-owner -C "$work"
fi
cd "$work/lean"
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.33.1"
nix develop "$record" --command lean --version
nix develop "$record" --command lake exe cache get
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "0df444a360eaa60ab8c11dca51a86af692955474"
if [[ "${2:-}" == "--prepare-only" ]]; then echo "Prepared project in $work/lean"; exit 0; fi
nix develop "$record" --command lake build +Main:olean
echo REPLAY_SOURCE_BUILD_PASSED
nix develop "$record" --command lake env lean "$record/Audit.lean"
echo REPLAY_AXIOM_AUDIT_PASSED
nix develop "$record" --command lake env leanchecker --fresh Main
echo REPLAY_FRESH_KERNEL_PASSED