import contextlib
import difflib
import hashlib
import io
import json
import subprocess
import tarfile
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import port
import port_build

ORIGINAL = 'theorem a : True := by\n  trivial\n'


def sha(data):
    return hashlib.sha256(data).hexdigest()


class PortBuildTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.work = self.root / 'work'
        self.tree = self.work / 'lean'
        self.patches = self.root / 'patches'
        self.patches.mkdir()
        files = {'src/Base.lean': ORIGINAL, 'src/Mid.lean': 'import Base\n', 'src/Top.lean': 'import Mid\n'}
        self.rows = [
            dict(id='M000001', module='Base', packet='P0001', depth=0, imports=[]),
            dict(id='M000002', module='Mid', packet='P0002', depth=1, imports=['M000001']),
            dict(id='M000003', module='Top', packet='P0003', depth=2, imports=['M000002']),
        ]
        for row in self.rows:
            row['source_sha256'] = sha(files['src/' + row['module'] + '.lean'].encode())
        self.write_archive(files)
        for rel, text in files.items():
            (self.tree / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.tree / rel).write_text(text)
        overrides = [(port_build, 'PARTS', self.root / 'parts.sha256'),
                     (port_build, 'PATCHES', self.patches),
                     (port, 'PRUNED', self.root / 'pruned.txt')]
        for module, name, value in overrides:
            change = patch.object(module, name, value)
            change.start()
            self.addCleanup(change.stop)

    def write_archive(self, files):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode='w:gz') as tar:
            for rel, text in files.items():
                data = text.encode()
                info = tarfile.TarInfo('lean/' + rel)
                info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
        data, parts = buffer.getvalue(), self.work / 'parts'
        parts.mkdir(parents=True)
        lines = []
        for i in range(3):
            chunk = data[i * len(data) // 3:(i + 1) * len(data) // 3]
            (parts / f'part0{i + 1}').write_bytes(chunk)
            lines.append(f'{sha(chunk)}  part0{i + 1}')
        (self.root / 'parts.sha256').write_text('\n'.join(lines) + '\n')

    def edit(self, rel, old, new):
        path = self.tree / rel
        path.write_text(path.read_text().replace(old, new))

    def run_diff(self, selection, out):
        args = SimpleNamespace(packet=selection, work=self.work, out=out)
        with patch.object(port_build.tasks, 'load', return_value=self.rows), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as err:
            return port_build.cmd_diff(args), err.getvalue()

    def test_imports_closure_is_transitive_and_excludes_members(self):
        by_id = {r['id']: r for r in self.rows}
        self.assertEqual([r['id'] for r in port_build.imports_closure(by_id, [self.rows[2]])],
                         ['M000001', 'M000002'])
        self.assertEqual([r['id'] for r in port_build.imports_closure(by_id, self.rows[1:])], ['M000001'])

    def test_packet_skips_pruned_members_but_preserves_imports(self):
        self.rows[1]['packet'] = 'P0001'
        port.PRUNED.write_text('# upstream pruning\nM000001\n')
        selected = port_build.packet(self.rows, 'P0001')
        self.assertEqual(selected, [self.rows[1]])
        by_id = {r['id']: r for r in self.rows}
        self.assertEqual(port_build.imports_closure(by_id, selected), [self.rows[0]])
        with self.assertRaisesRegex(SystemExit, 'pruned'):
            port_build.packet(self.rows, 'M000001')

    def test_originals_read_split_parts_and_reject_corruption(self):
        parts = self.work / 'parts'
        port_build.verify_parts(parts)
        self.assertEqual(port_build.originals(parts, ['src/Base.lean']), {'src/Base.lean': ORIGINAL.encode()})
        with self.assertRaises(SystemExit):
            port_build.originals(parts, ['src/Missing.lean'])
        (parts / 'part02').write_bytes(b'corrupt')
        with self.assertRaises(SystemExit):
            port_build.verify_parts(parts)

    def test_retarget_moves_pins_and_rejects_unexpected_lakefile(self):
        pins = dict(lean='leanprover/lean4:v4.36.0', mathlib='new',
                    replay_pins_unchanged=dict(lean='leanprover/lean4:v4.33.1', mathlib='old'))
        (self.tree / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        (self.tree / 'lakefile.toml').write_text('[[require]]\nname = "mathlib"\nrev = "old"\n')
        (self.tree / 'lake-manifest.json').write_text('{}')
        port_build.retarget(self.tree, pins)
        self.assertEqual((self.tree / 'lean-toolchain').read_text(), 'leanprover/lean4:v4.36.0\n')
        self.assertIn('rev = "new"', (self.tree / 'lakefile.toml').read_text())
        self.assertFalse((self.tree / 'lake-manifest.json').exists())
        (self.tree / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        with self.assertRaises(SystemExit):
            port_build.retarget(self.tree, pins)

    def test_diff_writes_clean_patches_and_flags_forbidden_constructs(self):
        self.edit('src/Base.lean', '  trivial', '  exact True.intro')
        status, err = self.run_diff('M000001', self.patches)
        self.assertEqual((status, err), (0, ''))
        text = (self.patches / 'M000001.patch').read_text()
        self.assertTrue(text.startswith('--- a/src/Base.lean\n+++ b/src/Base.lean\n@@ '))
        self.assertIn('+  exact True.intro', text)
        self.edit('src/Base.lean', '  exact True.intro', '  sorry')
        status, err = self.run_diff('M000001', self.patches)
        self.assertEqual(status, 1)
        self.assertIn('forbidden construct', err)
        (self.tree / 'src/Base.lean').write_text(ORIGINAL)
        status, err = self.run_diff('M000001', self.patches)
        self.assertEqual(status, 1)
        self.assertIn('no longer edited', err)

    def test_sync_imports_applies_each_patch_once_and_rejects_other_edits(self):
        self.edit('src/Base.lean', '  trivial', '  exact True.intro')
        self.run_diff('M000001', self.patches)
        (self.tree / 'src/Base.lean').write_text(ORIGINAL)
        imports = [self.rows[0]]
        with self.assertRaises(SystemExit):
            port_build.sync_imports(self.tree, imports, set())
        self.assertEqual(port_build.sync_imports(self.tree, imports, {'M000001'}), ['M000001'])
        self.assertIn('exact True.intro', (self.tree / 'src/Base.lean').read_text())
        self.assertEqual(port_build.sync_imports(self.tree, imports, {'M000001'}), [])
        self.edit('src/Base.lean', 'exact True.intro', 'exact trivial')
        with self.assertRaises(SystemExit):
            port_build.sync_imports(self.tree, imports, {'M000001'})

    def test_sync_imports_rejects_edits_outside_patch_without_changing_source(self):
        original = ORIGINAL + '\n' * 8 + 'def existing : Nat := 1\n'
        accepted = original.replace('  trivial', '  exact True.intro')
        row = dict(self.rows[0], source_sha256=sha(original.encode()))
        (self.patches / 'M000001.patch').write_text(''.join(difflib.unified_diff(
            original.splitlines(keepends=True), accepted.splitlines(keepends=True),
            fromfile='a/src/Base.lean', tofile='b/src/Base.lean')))
        source = self.tree / 'src/Base.lean'
        accepted = accepted.encode()
        extra = b'def extraUnrecorded : Nat := 42\n'
        for dirty in (accepted + extra, extra + accepted):
            with self.subTest(dirty=dirty):
                source.write_bytes(dirty)
                with self.assertRaisesRegex(SystemExit, 'differs from both'):
                    port_build.sync_imports(self.tree, [row], {'M000001'})
                self.assertEqual(source.read_bytes(), dirty)

    def test_sync_imports_rejects_patch_applied_to_wrong_duplicate_block(self):
        block = 'example : True := by\n  trivial\n' + '\n' * 8
        original = block + block
        accepted = original.replace('  trivial', '  exact True.intro', 1)
        dirty = block + block.replace('  trivial', '  exact True.intro', 1)
        row = dict(self.rows[0], source_sha256=sha(original.encode()))
        (self.patches / 'M000001.patch').write_text(''.join(difflib.unified_diff(
            original.splitlines(keepends=True), accepted.splitlines(keepends=True),
            fromfile='a/src/Base.lean', tofile='b/src/Base.lean')))
        source = self.tree / 'src/Base.lean'
        source.write_text(dirty)
        with self.assertRaisesRegex(SystemExit, 'differs from both'):
            port_build.sync_imports(self.tree, [row], {'M000001'})
        self.assertEqual(source.read_text(), dirty)

    def test_apply_patch_requires_an_exact_match(self):
        self.edit('src/Base.lean', '  trivial', '  exact True.intro')
        self.run_diff('M000001', self.patches)
        (self.tree / 'src/Base.lean').write_text('-- moved\n' + ORIGINAL)
        with self.assertRaises(SystemExit):
            port_build.apply_patch(self.tree, self.patches / 'M000001.patch')

    def test_check_ready_only_skips_members_with_unported_imports(self):
        (self.patches / 'M000001.json').write_text('{}')
        args = SimpleNamespace(packet='M000002', work=self.work, out=self.root / 'out', ready_only=True,
                               exclude=[])
        built = []
        with patch.object(port_build.tasks, 'load', return_value=self.rows), \
                patch.object(port_build, 'target', return_value={}), \
                patch.object(port_build, 'toolchain'), \
                patch.object(port_build, 'build', side_effect=lambda *a: built.append(a[3]['id']) or (0, 1.0)), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(port_build.cmd_check(args), 0)
            self.assertEqual(built, ['M000002'])
            args.packet = 'M000003'
            with self.assertRaises(SystemExit):
                port_build.cmd_check(args)
            # A member may wait on another ready member of its own packet, as in port.py show --ready-only.
            self.rows[2]['packet'] = 'P0002'
            args.packet, built[:] = 'P0002', []
            self.assertEqual(port_build.cmd_check(args), 0)
            self.assertEqual(built, ['M000002', 'M000003'])

    def test_reused_names_ignore_comments_and_other_identifiers(self):
        text = ('/-- A doc comment about IsLattice\n  spanning two lines -/\n'
                'theorem t : Submodule.IsLattice K M := by  -- not IsAddTorsionFree\n'
                '  exact ⟨IsZLattice.x, isLattice_foo, h.IsLatticeish⟩\n'
                'instance : IsMulTorsionFree G := inferInstance\n')
        self.assertEqual(port_build.reused_names(text), [(3, 'IsLattice'), (5, 'IsMulTorsionFree')])

    def test_reused_norm_name_distinguishes_the_unguarded_formula(self):
        text = ("#check MeasureTheory.eLpNorm\n"
                "#check MeasureTheory.eLpNorm'\n"
                "#check eLpNorm f 2 μ\n")
        self.assertEqual(port_build.reused_names(text), [(1, 'eLpNorm'), (3, 'eLpNorm')])

    def test_reused_names_multiplicity_and_no_atoms(self):
        text = ("def v : ℕ := multiplicity P I\n"
                "#check emultiplicity P I\n"
                "#check multiplicity_eq_zero_of_not_dvd\n"
                "instance : MeasureTheory.NoAtoms μ := inferInstance\n"
                "instance : NullSingletonClass μ := inferInstance\n")
        self.assertEqual(port_build.reused_names(text), [(1, 'multiplicity'), (4, 'NoAtoms')])

    def test_check_warns_about_unchanged_modules_with_reused_names(self):
        (self.tree / 'src/Base.lean').write_text('def L : Prop := Submodule.IsLattice K M\n')
        self.rows[0]['source_sha256'] = sha((self.tree / 'src/Base.lean').read_bytes())
        args = SimpleNamespace(packet='M000001', work=self.work, out=self.root / 'out', ready_only=False,
                               exclude=[])
        with patch.object(port_build.tasks, 'load', return_value=self.rows), \
                patch.object(port_build, 'target', return_value={}), \
                patch.object(port_build, 'toolchain'), \
                patch.object(port_build, 'build', return_value=(0, 1.0)), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(port_build.cmd_check(args), 0)
        self.assertIn('line 1: IsLattice, whose pinned meaning is now Submodule.IsFullLattice', output.getvalue())
        self.assertEqual(json.loads((self.root / 'out/results.json').read_text())[0]['reused_names'], ['1:IsLattice'])

    def records(self, selection, note_map, reviewed=(), ready_only=False, exclude=()):
        pins = dict(lean='leanprover/lean4:v4.36.0', mathlib='new')
        notes = self.root / 'notes.json'
        notes.write_text(json.dumps(note_map))
        args = SimpleNamespace(packet=selection, work=self.work, evidence='https://example.test/receipt.json',
                               notes=notes, patches=None, force=False, reviewed=list(reviewed),
                               ready_only=ready_only, exclude=list(exclude))
        with patch.object(port_build.tasks, 'load', return_value=self.rows), \
                patch.object(port_build, 'target', return_value=pins), \
                contextlib.redirect_stdout(io.StringIO()):
            port_build.cmd_records(args)
        return pins

    def test_records_refuse_unreviewed_reused_names_and_unsaved_edits(self):
        (self.tree / 'src/Base.lean').write_text('def L : Prop := Submodule.IsLattice K M\n')
        self.rows[0]['source_sha256'] = sha((self.tree / 'src/Base.lean').read_bytes())
        with self.assertRaises(SystemExit) as refused:
            self.records('M000001', {})
        self.assertIn('M000001 line 1: IsLattice', str(refused.exception))
        self.records('M000001', {}, reviewed=['M000001'])
        self.assertEqual(json.loads((self.patches / 'M000001.json').read_text())['notes'], 'unchanged')
        self.edit('src/Mid.lean', 'Base', 'Base\n-- edited')
        with self.assertRaises(SystemExit) as refused:
            self.records('M000002', {})
        self.assertIn('has no patch', str(refused.exception))

    def test_link_tree_shares_files_and_keeps_symlinks(self):
        src = self.root / 'packages'
        (src / 'mathlib/.lake/build').mkdir(parents=True)
        olean = src / 'mathlib/.lake/build/Mathlib.olean'
        olean.write_bytes(b'olean')
        (src / 'link').symlink_to('mathlib')
        dst = self.root / 'fresh/packages'
        port_build.link_tree(src, dst)
        copied = dst / 'mathlib/.lake/build/Mathlib.olean'
        self.assertEqual(copied.read_bytes(), b'olean')
        self.assertTrue(copied.samefile(olean))
        self.assertTrue((dst / 'link').is_symlink())

    def test_link_tree_copies_when_hardlinks_fail(self):
        src = self.root / 'packages'
        src.mkdir()
        (src / 'a.olean').write_bytes(b'olean')
        dst = self.root / 'fresh/packages'
        with patch.object(port_build.os, 'link', side_effect=OSError('cross-device link')):
            port_build.link_tree(src, dst)
        self.assertEqual((dst / 'a.olean').read_bytes(), b'olean')
        self.assertFalse((dst / 'a.olean').samefile(src / 'a.olean'))

    def test_ready_selection_splits_ready_and_remaining_members(self):
        self.rows[2]['packet'] = 'P0002'
        members = port_build.packet(self.rows, 'P0002')
        self.assertEqual(port_build.ready_selection(members, False), (members, []))
        with self.assertRaises(SystemExit):
            port_build.ready_selection(members, True)
        (self.patches / 'M000001.json').write_text('{}')
        self.assertEqual(port_build.ready_selection(members, True), (members, []))
        waiting = dict(id='M000004', module='Waiting', packet='P0002', depth=1, imports=['M000099'])
        self.assertEqual(port_build.ready_selection(members + [waiting], True), (members, [waiting]))

    def test_ready_selection_excludes_members_and_their_dependents(self):
        self.rows[2]['packet'] = 'P0002'
        (self.patches / 'M000001.json').write_text('{}')
        side = dict(id='M000005', module='Side', packet='P0002', depth=1, imports=['M000001'])
        mid, top = port_build.packet(self.rows, 'P0002')
        members = [mid, top, side]
        # Top imports the excluded Mid, so it waits as remaining; Mid itself is listed by neither.
        self.assertEqual(port_build.ready_selection(members, True, ['M000002']), ([side], [top]))
        with self.assertRaises(SystemExit):
            port_build.ready_selection(members, False, ['M000002'])
        with self.assertRaises(SystemExit):
            port_build.ready_selection(members, True, ['M000099'])
        # Excluding a member that is already ported means the selection is out of date.
        (self.patches / 'M000005.json').write_text('{}')
        with self.assertRaises(SystemExit):
            port_build.ready_selection(members, True, ['M000005'])

    def test_ready_selection_does_not_list_ported_members_as_remaining(self):
        self.rows[2]['packet'] = 'P0002'
        (self.patches / 'M000001.json').write_text('{}')
        (self.patches / 'M000002.json').write_text('{}')
        mid, top = port_build.packet(self.rows, 'P0002')
        self.assertEqual(port_build.ready_selection([mid, top], True), ([top], []))

    def test_records_skip_excluded_members(self):
        (self.patches / 'M000001.json').write_text('{}')
        (self.tree / 'src/Side.lean').write_text('import Base\n')
        self.rows += [dict(id='M000006', module='Side', packet='P0002', depth=1, imports=['M000001'],
                           source_sha256=sha(b'import Base\n'))]
        self.records('P0002', {}, ready_only=True, exclude=['M000006'])
        self.assertTrue((self.patches / 'M000002.json').exists())
        self.assertFalse((self.patches / 'M000006.json').exists())

    def test_records_ready_only_leaves_waiting_members_unrecorded(self):
        (self.patches / 'M000001.json').write_text('{}')
        (self.tree / 'src/Waiting.lean').write_text('import Missing\n')
        self.rows += [dict(id='M000004', module='Waiting', packet='P0002', depth=1, imports=['M000099'],
                           source_sha256=sha(b'import Missing\n'))]
        self.records('P0002', {}, ready_only=True)
        self.assertTrue((self.patches / 'M000002.json').exists())
        self.assertFalse((self.patches / 'M000004.json').exists())
        # Without --ready-only the waiting member would be recorded as unchanged although it never built.
        (self.patches / 'M000002.json').unlink()
        self.records('P0002', {})
        self.assertTrue((self.patches / 'M000004.json').exists())

    def test_records_pair_notes_with_patches(self):
        (self.patches / 'M000002.patch').write_text('patch')
        write = self.records

        for selection, note_map in [('M000002', {}), ('M000001', {'M000001': 'why'}), ('M000001', {'M000002': 'why'})]:
            with self.subTest(selection=selection, notes=note_map), self.assertRaises(SystemExit):
                write(selection, note_map)
        pins = write('M000002', {'M000002': 'Renamed lemma.'})
        record = json.loads((self.patches / 'M000002.json').read_text())
        self.assertEqual((record['notes'], record['source_sha256'], record['lean']),
                         ('Renamed lemma.', self.rows[1]['source_sha256'], pins['lean']))
        with self.assertRaises(SystemExit):
            write('M000002', {'M000002': 'Again.'})


if __name__ == '__main__':
    unittest.main()
