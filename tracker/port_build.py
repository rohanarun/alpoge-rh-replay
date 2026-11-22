"""Build port work on the target toolchain and reproduce its evidence (see PORTING.md).

  python3 tracker/port_build.py prepare WORK [--parts DIR]   # port tree in WORK/lean on the target pins
  python3 tracker/port_build.py check P0123 WORK [--ready-only]  # build each module, list failures
  python3 tracker/port_build.py diff P0123 WORK               # write patches for edited modules
  python3 tracker/port_build.py reproduce P0123 WORK OUT [--ready-only]  # fresh tree + patches, receipt
  python3 tracker/port_build.py records P0123 WORK --evidence URL [--ready-only]  # port/patches/<ID>.json

WORK holds the verified archive parts, the Lean toolchain, the Mathlib cache and the
port tree. Edit modules in WORK/lean/src, then `diff` turns the edits into patches
against the pinned sources. Project imports of a packet are built with their merged
patches from port/patches, so deeper packets build the same tree a maintainer assembles.
"""
import argparse
import datetime
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from pathlib import Path

import tasks
from port import PATCHES, ROOT, pruned, ready_members
from validate_ports import BLOCK_COMMENT_RE, strip_lean_comments, validate_patch_content

TARGET = ROOT / 'port' / 'target.json'
PARTS = ROOT / 'parts.sha256'
ARCHIVE_URL = 'https://alpo.ge/lean.tar.gz.'

# Names Mathlib reused for a different notion between the pinned and target revisions,
# with where the pinned meaning went. Unchanged text that mentions one can build and
# still say something else on the target (#26196).
REUSED_NAMES = {
    'IsLattice': 'Submodule.IsFullLattice (the pinned IsLattice also required span_eq_top)',
    'IsAddTorsionFree': 'HasUniqueDiv (the new IsAddTorsionFree adds an AddCommute hypothesis, '
                        'so the meaning is kept in commutative monoids)',
    'IsMulTorsionFree': 'HasUniqueRoots (the new IsMulTorsionFree adds a Commute hypothesis, '
                        'so the meaning is kept in commutative monoids)',
    'eLpNorm': "eLpNorm' at finite nonzero exponents without a.e. strong measurability "
               "(the target eLpNorm returns ∞ for functions that are not a.e. strongly measurable)",
    'NoAtoms': 'NullSingletonClass (the pinned NoAtoms was an alias of NullSingletonClass, '
               'singletons are null; the target NoAtoms is a new class that forbids atoms)',
    'multiplicity': '(emultiplicity a b).untopD 1 (the target multiplicity is (emultiplicity a b).toNat, '
                    'so it is 0 instead of 1 when the multiplicity is infinite)',
}
REUSED_RE = re.compile(r"(?<![\w.'])(?:[A-Z]\w*\.)*(" + '|'.join(REUSED_NAMES) + r")(?![\w'])")


def reused_names(text):
    """Line numbers and names of reused Mathlib names in Lean code, ignoring comments."""
    text = BLOCK_COMMENT_RE.sub(lambda m: '\n' * m.group().count('\n'), text)
    return [(n, m.group(1)) for n, line in enumerate(text.splitlines(), 1)
            for m in REUSED_RE.finditer(strip_lean_comments(line))]


def target():
    return json.loads(TARGET.read_text())


def source_relpath(row):
    return 'src/' + row['module'].replace('.', '/') + '.lean'


def part_hashes():
    return [line.split() for line in PARTS.read_text().splitlines() if line.strip()]


def verify_parts(folder):
    for expected, name in part_hashes():
        if not (folder / name).is_file() or tasks.digest(folder / name) != expected:
            raise SystemExit(f'Archive part {name} does not match parts.sha256')


class ChainedParts(io.RawIOBase):
    """Read the archive parts in order as one stream."""

    def __init__(self, folder):
        self.files = [(folder / name).open('rb') for _, name in part_hashes()]

    def readable(self):
        return True

    def readinto(self, buffer):
        while self.files:
            n = self.files[0].readinto(buffer)
            if n:
                return n
            self.files.pop(0).close()
        return 0

    def close(self):
        for f in self.files:
            f.close()
        super().close()


def open_archive(folder):
    return tarfile.open(fileobj=io.BufferedReader(ChainedParts(folder)), mode='r|gz')


def extract(folder, dest):
    with open_archive(folder) as tar:
        if hasattr(tarfile, 'data_filter'):
            tar.extractall(dest, filter='data')
        else:
            tar.extractall(dest)


def originals(folder, relpaths):
    """Return the pinned bytes of the given tree-relative paths, read from the archive parts."""
    wanted = {'lean/' + p: p for p in relpaths}
    found = {}
    with open_archive(folder) as tar:
        for member in tar:
            if member.name in wanted:
                found[wanted[member.name]] = tar.extractfile(member).read()
                if len(found) == len(wanted):
                    break
    missing = sorted(set(relpaths) - set(found))
    if missing:
        raise SystemExit('Not in the archive: ' + ', '.join(missing))
    return found


def retarget(tree, pins):
    """Point the pinned project at the port toolchain and Mathlib."""
    old = pins['replay_pins_unchanged']
    if (tree / 'lean-toolchain').read_text().strip() != old['lean']:
        raise SystemExit('Unexpected lean-toolchain in the archive')
    lakefile = tree / 'lakefile.toml'
    text = lakefile.read_text()
    line = f'rev = "{old["mathlib"]}"'
    if text.count(line) != 1:
        raise SystemExit('Expected exactly one pinned Mathlib rev in lakefile.toml')
    lakefile.write_text(text.replace(line, f'rev = "{pins["mathlib"]}"'))
    (tree / 'lean-toolchain').write_text(pins['lean'] + '\n')
    (tree / 'lake-manifest.json').unlink()


def environment(work):
    return dict(os.environ, ELAN_HOME=str(work / 'elan'), XDG_CACHE_HOME=str(work / 'cache'))


def toolchain(tree, env, pins):
    """Return the Lean version line and Mathlib commit, checked against the port target."""
    version = subprocess.check_output(['elan', 'run', pins['lean'], 'lean', '--version'],
                                      cwd=tree, env=env, text=True).strip()
    mathlib = subprocess.check_output(['git', '-C', str(tree / '.lake/packages/mathlib'), 'rev-parse', 'HEAD'],
                                      text=True).strip()
    expected = pins['lean'].rsplit(':v', 1)[-1]
    if not version.startswith(f'Lean (version {expected},') or mathlib != pins['mathlib']:
        raise SystemExit(f'Tree is not on the port target: {version}, Mathlib {mathlib}')
    return version, mathlib


def packet(rows, selection):
    members = [r for r in rows if selection in (r['id'], r['packet'])]
    if not members:
        raise SystemExit('Unknown packet or module ID: ' + selection)
    omitted = pruned()
    active = [r for r in members if r['id'] not in omitted]
    if not active:
        raise SystemExit('Selection contains only pruned modules: ' + selection)
    return active


def ready_selection(members, ready_only, exclude=()):
    """The members to work on and, with --ready-only, the unported members left for later.

    Excluded members (for example ones another contributor is still porting) are left out together
    with the members that import them; those dependents are listed as remaining."""
    exclude = set(exclude)
    if exclude and not ready_only:
        raise SystemExit('--exclude needs --ready-only')
    unknown = sorted(exclude - {r['id'] for r in members})
    if unknown:
        raise SystemExit('Excluded modules outside the selection: ' + ', '.join(unknown))
    if not ready_only:
        return members, []
    done = {p.stem for p in PATCHES.glob('M*.json')}
    recorded = sorted(exclude & done)
    if recorded:
        raise SystemExit('Excluded modules already have records on main: ' + ', '.join(recorded))
    ready = ready_members([r for r in members if r['id'] not in exclude], done)
    if not ready:
        raise SystemExit('No member of the selection is ready to build')
    return ready, [r for r in members if r not in ready and r['id'] not in done | exclude]


def imports_closure(by_id, members):
    """Project modules the members import, directly or indirectly, excluding the members."""
    own = {r['id'] for r in members}
    seen, stack = set(), [i for r in members for i in r['imports']]
    while stack:
        i = stack.pop()
        if i in own or i in seen:
            continue
        seen.add(i)
        stack.extend(by_id[i]['imports'])
    return [by_id[i] for i in sorted(seen)]


def run_patch(tree, patch, *flags):
    with patch.open('rb') as stream:
        return subprocess.run(['patch', '-p1', '--fuzz=0', '--no-backup-if-mismatch', '--batch', *flags],
                              cwd=tree, stdin=stream, capture_output=True, text=True)


def apply_patch(tree, patch):
    result = run_patch(tree, patch)
    if result.returncode or 'offset' in result.stdout or 'fuzz' in result.stdout:
        raise SystemExit(f'{patch.name} does not apply cleanly:\n{result.stdout}{result.stderr}')
    return result.stdout.strip()


def matches_port_patch(tree, patch, row):
    """Check the entire source is exactly the pinned source plus its port patch."""
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / source_relpath(row)
        copy.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(tree / source_relpath(row), copy)
        candidate = copy.read_bytes()
        result = run_patch(Path(tmp), patch, '-R')
        if result.returncode or tasks.digest(copy) != row['source_sha256']:
            return False
        try:
            apply_patch(Path(tmp), patch)
        except SystemExit:
            return False
        return copy.read_bytes() == candidate


def sync_imports(tree, imports, ported):
    """Give each project import its merged port patch, leaving already patched files alone."""
    missing = [r['id'] for r in imports if r['id'] not in ported]
    if missing:
        raise SystemExit('Unported project imports: ' + ', '.join(missing))
    applied = []
    for r in imports:
        patch = PATCHES / f"{r['id']}.patch"
        pristine = tasks.digest(tree / source_relpath(r)) == r['source_sha256']
        if pristine and patch.exists():
            apply_patch(tree, patch)
            applied.append(r['id'])
        elif not pristine and not (patch.exists() and matches_port_patch(tree, patch, r)):
            raise SystemExit(f"{r['id']} differs from both its pinned source and its port patch")
    return applied


def check_sources(tree, rows):
    changed = [r['id'] for r in rows if tasks.digest(tree / source_relpath(r)) != r['source_sha256']]
    if changed:
        raise SystemExit('Sources differ from the pinned archive: ' + ', '.join(changed))


def build(tree, env, pins, row, log):
    command = ['lake', '--no-cache', 'build', f"+{row['module']}:olean"]
    start = time.monotonic()
    with log.open('wb') as stream:
        status = subprocess.run(['elan', 'run', pins['lean'], *command], cwd=tree, env=env,
                                stdout=stream, stderr=subprocess.STDOUT).returncode
    return status, round(time.monotonic() - start, 1)


def first_errors(text, limit=3):
    lines = [l for l in text.splitlines() if l.startswith('error:') and l != 'error: build failed']
    return lines[:limit]


def summary_lines(text, module):
    keep = ('error', 'Build completed')
    return [l for l in text.splitlines()
            if l.startswith(keep) or (l[:1] in '✔⚠✖' and f' {module}' in l and 'Built' in l)]


def cmd_prepare(args):
    work, pins = args.work.resolve(), target()
    if work.exists() and any(work.iterdir()):
        raise SystemExit(f'{work} is not empty')
    parts = work / 'parts'
    parts.mkdir(parents=True)
    for _, name in part_hashes():
        if args.parts:
            shutil.copyfile(args.parts / name, parts / name)
        else:
            subprocess.run(['curl', '--fail', '--location', '--retry', '4', '--output', str(parts / name),
                            ARCHIVE_URL + name], check=True)
    verify_parts(parts)
    extract(parts, work)
    tree, env = work / 'lean', environment(work)
    retarget(tree, pins)
    subprocess.run(['elan', 'toolchain', 'install', pins['lean']], env=env, check=True)
    subprocess.run(['elan', 'run', pins['lean'], 'lake', 'update'], cwd=tree, env=env, check=True)
    if (tree / '.lake/packages/mathlib/lean-toolchain').read_text().strip() != pins['lean']:
        raise SystemExit('Mathlib at the target commit expects a different toolchain')
    subprocess.run(['elan', 'run', pins['lean'], 'lake', 'exe', 'cache', 'get'], cwd=tree, env=env, check=True)
    version, mathlib = toolchain(tree, env, pins)
    print(f'Prepared {tree}: {version}, Mathlib {mathlib}')


def cmd_check(args):
    work, pins, rows = args.work.resolve(), target(), tasks.load()
    tree, env = work / 'lean', environment(work)
    members = packet(rows, args.packet)
    toolchain(tree, env, pins)
    by_id = {r['id']: r for r in rows}
    ported = {p.stem for p in PATCHES.glob('M*.json')}
    members, skipped = ready_selection(members, args.ready_only, args.exclude)
    if skipped:
        print('Skipping members that wait for unported or excluded imports:', ' '.join(r['id'] for r in skipped))
    applied = sync_imports(tree, imports_closure(by_id, members), ported)
    if applied:
        print('Applied port patches to imports:', ' '.join(applied))
    out = (args.out or work / f'check-{args.packet}').resolve()
    (out / 'logs').mkdir(parents=True, exist_ok=True)
    results = []
    for r in members:
        log = out / 'logs' / f"{r['id']}.log"
        status, seconds = build(tree, env, pins, r, log)
        edited = tasks.digest(tree / source_relpath(r)) != r['source_sha256']
        reused = [] if edited else reused_names((tree / source_relpath(r)).read_text())
        results.append(dict(id=r['id'], module=r['module'], exit_code=status, seconds=seconds,
                            edited=edited, reused_names=[f'{n}:{name}' for n, name in reused]))
        if status:
            print(f"{r['id']} {r['module']} failed")
            for line in first_errors(log.read_text(errors='replace')):
                print('    ' + line)
        elif reused:
            print(f"{r['id']} {r['module']} builds unchanged but mentions reused Mathlib names:")
            for n, name in reused:
                print(f'    line {n}: {name}, whose pinned meaning is now {REUSED_NAMES[name]}')
    (out / 'results.json').write_text(json.dumps(results, indent=2, ensure_ascii=False) + '\n')
    failed = sum(1 for r in results if r['exit_code'])
    print(f'{len(results) - failed} of {len(results)} modules built; logs in {out}')
    return int(bool(failed))


def cmd_diff(args):
    work, rows = args.work.resolve(), tasks.load()
    tree, out = work / 'lean', args.out.resolve()
    members = packet(rows, args.packet)
    edited = [r for r in members if tasks.digest(tree / source_relpath(r)) != r['source_sha256']]
    pristine = originals(work / 'parts', [source_relpath(r) for r in edited])
    out.mkdir(parents=True, exist_ok=True)
    problems = []
    with tempfile.TemporaryDirectory() as tmp:
        for r in edited:
            rel = source_relpath(r)
            original = Path(tmp) / f"{r['id']}.lean"
            original.write_bytes(pristine[rel])
            if tasks.digest(original) != r['source_sha256']:
                raise SystemExit(f"Archive copy of {r['id']} does not match its pinned hash")
            result = subprocess.run(['diff', '-u', '--label', 'a/' + rel, '--label', 'b/' + rel,
                                     str(original), str(tree / rel)], capture_output=True)
            if result.returncode != 1:
                raise SystemExit(f"diff failed for {r['id']}: {result.stderr.decode()}")
            patch = out / f"{r['id']}.patch"
            patch.write_bytes(result.stdout)
            problems += validate_patch_content(patch, rel)
            changed = sum(1 for l in result.stdout.decode().splitlines() if l[:1] in '+-' and l[:3] not in ('+++', '---'))
            print(f"{patch}: {changed} changed lines")
    for stale in sorted(set(r['id'] for r in members) - set(r['id'] for r in edited)):
        if (out / f'{stale}.patch').exists():
            problems.append(f'{stale}.patch: the module is no longer edited; remove the patch')
    for problem in problems:
        print(problem, file=sys.stderr)
    return int(bool(problems))


def link_tree(src, dst):
    """Copy a directory tree, hardlinking regular files where the filesystem allows it.

    The Lake packages (Mathlib and its dependencies, about 7 GB of build outputs) are only read
    while a packet is rebuilt, so the fresh tree can share them with the work tree. Separate
    copies cost the disk space and, when several packets are rebuilt at once, let the page cache
    hold one copy of Mathlib per tree, which thrashes on machines with less memory than that."""
    def link_or_copy(source, target):
        try:
            os.link(source, target)
        except OSError:
            shutil.copy2(source, target)
    shutil.copytree(src, dst, symlinks=True, copy_function=link_or_copy)


def cmd_reproduce(args):
    work, pins, rows = args.work.resolve(), target(), tasks.load()
    out, patches = args.out.resolve(), (args.patches or PATCHES).resolve()
    if out.exists():
        raise SystemExit(f'{out} already exists')
    members, remaining = ready_selection(packet(rows, args.packet), args.ready_only, args.exclude)
    by_id = {r['id']: r for r in rows}
    imports = imports_closure(by_id, members)
    name = args.packet
    (out / 'logs').mkdir(parents=True)
    log = (out / f'{name}-build.log').open('w')

    def say(line=''):
        print(line)
        log.write(line + '\n')
        log.flush()

    started = datetime.datetime.now(datetime.timezone.utc)
    verify_parts(work / 'parts')
    say(f'== archive: all {len(part_hashes())} parts match parts.sha256')
    extract(work / 'parts', out)
    tree, env = out / 'lean', environment(work)
    check_sources(tree, members + imports)
    say(f'== sources: all {len(members)} packet and {len(imports)} import source hashes match')
    if remaining:
        say(f'== remaining: {len(remaining)} members wait for unported imports and are not built: '
            + ' '.join(r['id'] for r in remaining))
    if args.exclude:
        say(f'== excluded: {len(args.exclude)} members are left to other contributors and are not built: '
            + ' '.join(sorted(args.exclude)))
    retarget(tree, pins)
    shutil.copyfile(work / 'lean/lake-manifest.json', tree / 'lake-manifest.json')
    link_tree(work / 'lean/.lake/packages', tree / '.lake/packages')
    version, mathlib = toolchain(tree, env, pins)
    say(f'== toolchain: {version}; Mathlib {mathlib}')
    applied = []
    for r, folder in [(r, PATCHES) for r in imports] + [(r, patches) for r in members]:
        patch = folder / f"{r['id']}.patch"
        if r in imports and r['id'] not in {p.stem for p in PATCHES.glob('M*.json')}:
            raise SystemExit(f"Unported project import {r['id']}")
        if patch.exists():
            say(f"== patch {r['id']}: {apply_patch(tree, patch)}")
            applied.append(dict(id=r['id'], role='import' if r in imports else 'target',
                                patch_sha256=tasks.digest(patch)))
    say(f'== build: lake --no-cache build +<Module>:olean for each of {len(members)} modules')
    modules = []
    for r in members:
        module_log = out / 'logs' / f"{r['id']}.log"
        status, seconds = build(tree, env, pins, r, module_log)
        say(f"{r['id']} {r['module']} exit={status} {seconds}s")
        for line in summary_lines(module_log.read_text(errors='replace'), r['module']):
            say('    ' + line)
        olean = tree / '.lake/build/lib/lean' / (r['module'].replace('.', '/') + '.olean')
        patch = patches / f"{r['id']}.patch"
        modules.append(dict(id=r['id'], module=r['module'], source_sha256=r['source_sha256'],
                            patch_sha256=tasks.digest(patch) if patch.exists() else None,
                            built_source_sha256=tasks.digest(tree / source_relpath(r)),
                            olean_sha256=tasks.digest(olean) if status == 0 and olean.exists() else None,
                            log_sha256=tasks.digest(module_log), exit_code=status, seconds=seconds))
    failed = sum(1 for m in modules if m['exit_code'])
    say(f'== done: {len(modules) - failed} of {len(modules)} modules built')
    log.close()
    with tarfile.open(out / f'{name}-module-logs.tar.gz', 'w:gz') as tar:
        for m in modules:
            tar.add(out / 'logs' / f"{m['id']}.log", arcname=f"{m['id']}.log")
    receipt = dict(target=name, issue=f'https://github.com/{tasks.repo}/issues/{args.issue}' if args.issue else None,
                   toolchain=version, mathlib=mathlib,
                   inputs_manifest_sha256=tasks.digest(PARTS),
                   started_utc=started.isoformat(),
                   ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   host=tasks.host_resources(),
                   command='lake --no-cache build +<Module>:olean, one run per module, in a fresh tree '
                           'from the pinned archive plus port patches',
                   patches=applied, build_log_sha256=tasks.digest(out / f'{name}-build.log'), modules=modules,
                   remaining=[r['id'] for r in remaining], excluded=sorted(args.exclude))
    (out / f'{name}-receipt.json').write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
    print(f'Evidence in {out}: {name}-build.log, {name}-receipt.json, {name}-module-logs.tar.gz')
    return int(bool(failed))


def cmd_records(args):
    pins, rows = target(), tasks.load()
    members, remaining = ready_selection(packet(rows, args.packet), args.ready_only, args.exclude)
    patches = (args.patches or PATCHES).resolve()
    notes = json.loads(args.notes.read_text()) if args.notes else {}
    unknown = sorted(set(notes) - {r['id'] for r in members})
    if unknown:
        raise SystemExit('Notes for modules outside the selection: ' + ', '.join(unknown))
    tree = args.work.resolve() / 'lean'
    records, flagged = {}, []
    for r in members:
        patched = (patches / f"{r['id']}.patch").exists()
        note = notes.get(r['id'], 'unchanged')
        if patched == (note == 'unchanged'):
            raise SystemExit(f"{r['id']}: a patched module needs a note, and only a patched module can have one")
        if (PATCHES / f"{r['id']}.json").exists() and not args.force:
            raise SystemExit(f"{r['id']} already has a record; pass --force to replace it")
        if not patched:
            source = tree / source_relpath(r)
            if tasks.digest(source) != r['source_sha256']:
                raise SystemExit(f"{r['id']} is edited in {tree} but has no patch; run diff first")
            if r['id'] not in args.reviewed:
                flagged += [f"{r['id']} line {n}: {name}, whose pinned meaning is now {REUSED_NAMES[name]}"
                            for n, name in reused_names(source.read_text())]
        records[r['id']] = dict(module=r['module'], source_sha256=r['source_sha256'], lean=pins['lean'],
                                mathlib=pins['mathlib'], notes=note, evidence=args.evidence)
    if flagged:
        raise SystemExit('Unchanged modules mention reused Mathlib names. Patch them, or pass --reviewed ID '
                         'once every use keeps its pinned meaning:\n  ' + '\n  '.join(flagged))
    for mid, record in records.items():
        if patches != PATCHES.resolve() and (patches / f'{mid}.patch').exists():
            shutil.copyfile(patches / f'{mid}.patch', PATCHES / f'{mid}.patch')
        (PATCHES / f'{mid}.json').write_text(json.dumps(record, indent=2, ensure_ascii=False) + '\n')
    print(f'Wrote {len(records)} records, {sum(n != "unchanged" for n in notes.values())} with patches')
    if remaining:
        print('Left for later, waiting for unported imports:', ' '.join(r['id'] for r in remaining))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('prepare', help='extract and retarget the pinned archive in WORK/lean')
    p.add_argument('work', type=Path)
    p.add_argument('--parts', type=Path, help='copy archive parts from this folder instead of downloading')
    p = sub.add_parser('check', help='build each module of a packet in the work tree')
    p.add_argument('packet')
    p.add_argument('work', type=Path)
    p.add_argument('--out', type=Path, help='logs and results folder (default WORK/check-<ID>)')
    p.add_argument('--ready-only', action='store_true',
                   help='build only the members port.py show --ready-only lists')
    p.add_argument('--exclude', action='append', default=[], metavar='ID',
                   help='with --ready-only, leave out this member and the members that import it')
    p = sub.add_parser('diff', help='write patches for edited modules of a packet')
    p.add_argument('packet')
    p.add_argument('work', type=Path)
    p.add_argument('--out', type=Path, default=PATCHES, help='patch folder (default port/patches)')
    p = sub.add_parser('reproduce', help='rebuild a packet from the pinned archive plus patches')
    p.add_argument('packet')
    p.add_argument('work', type=Path)
    p.add_argument('out', type=Path)
    p.add_argument('--patches', type=Path, help="the packet's patch folder (default port/patches)")
    p.add_argument('--issue', type=int, help='Port issue number to record in the receipt')
    p.add_argument('--ready-only', action='store_true',
                   help='build only the ready members and list the rest as remaining in the receipt')
    p.add_argument('--exclude', action='append', default=[], metavar='ID',
                   help='with --ready-only, leave out this member and the members that import it')
    p = sub.add_parser('records', help='write port/patches/<ID>.json for every module of a packet')
    p.add_argument('packet')
    p.add_argument('work', type=Path)
    p.add_argument('--evidence', required=True, help='URL of the published receipt')
    p.add_argument('--ready-only', action='store_true',
                   help='write records only for the ready members, as for reproduce --ready-only')
    p.add_argument('--exclude', action='append', default=[], metavar='ID',
                   help='with --ready-only, leave out this member and the members that import it')
    p.add_argument('--reviewed', action='append', default=[], metavar='ID',
                   help='record an unchanged module that mentions a reused Mathlib name')
    p.add_argument('--notes', type=Path, help='JSON object of module ID to note for patched modules')
    p.add_argument('--patches', type=Path, help="the packet's patch folder (default port/patches)")
    p.add_argument('--force', action='store_true', help='replace existing records')
    args = parser.parse_args(argv)
    return {'prepare': cmd_prepare, 'check': cmd_check, 'diff': cmd_diff,
            'reproduce': cmd_reproduce, 'records': cmd_records}[args.command](args) or 0


if __name__ == '__main__':
    sys.exit(main())
