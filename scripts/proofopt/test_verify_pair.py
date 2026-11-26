import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from verify_pair import PROOF, PROTECTED, git, plan, run


class PairTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.g('init', '-q')
        self.g('config', 'user.name', 'ProofOpt test')
        self.g('config', 'user.email', 'test@example.invalid')
        for name in (*PROTECTED, PROOF):
            p = self.repo / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('original\n')
        (self.repo / 'lean-toolchain').write_text('leanprover/lean4:test\n')
        (self.repo / 'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': 'locked'}]}))
        (self.repo / '.gitignore').write_text('.lake/\n')
        self.base = self.commit('base')
        (self.repo / PROOF).write_text('candidate\n')
        self.candidate = self.commit('candidate')
        binpath = self.root / 'bin'
        binpath.mkdir()
        lake = binpath / 'lake'
        lake.write_text('#!/bin/sh\nset -eu\nprintf "%s %s %s\\n" "$*" "${LAKE_ARTIFACT_CACHE:-unset}" "${LEAN_NUM_THREADS:-unset}"\nif [ "${FAIL_BUILD:-0}" = 1 ] && [ "$*" = build ]; then exit 9; fi\nif [ "$*" = build ]; then mkdir -p .lake/build; fi\n')
        lake.chmod(0o755)
        bwrap = binpath / 'bwrap'
        bwrap.write_text('#!/bin/sh\nexit 0\n')
        bwrap.chmod(0o755)
        self.env = patch.dict(os.environ, {'PATH': str(binpath)+os.pathsep+os.environ['PATH']})
        self.env.start()
        self.addCleanup(self.env.stop)

    def g(self, *args):
        return git(self.repo, *args)

    def commit(self, msg):
        self.g('add', '.')
        self.g('commit', '-qm', msg)
        return self.g('rev-parse', 'HEAD')

    def test_exact_diff(self):
        p = plan(self.repo, self.base, self.candidate)
        self.assertEqual(p['changed_path'], PROOF)
        self.assertEqual(len(p['protected_blobs']), 10)
        self.assertNotEqual(p['before_blob'], p['after_blob'])
        self.assertEqual(p['mathlib'], 'locked')

    def test_protected_change_rejected(self):
        (self.repo / 'src/Challenge.lean').write_text('changed')
        with self.assertRaises(ValueError):
            plan(self.repo, self.base, self.commit('bad'))

    def test_extra_file_rejected(self):
        (self.repo / 'extra').write_text('extra')
        with self.assertRaises(ValueError):
            plan(self.repo, self.base, self.commit('bad'))

    def test_moving_ref_rejected(self):
        with self.assertRaises(ValueError):
            plan(self.repo, self.base, 'HEAD')

    def test_reverse_ancestry_rejected(self):
        with self.assertRaises(ValueError):
            plan(self.repo, self.candidate, self.base)

    def test_incremental(self):
        out = self.root / 'inc'
        r = run(self.repo, out, self.base, self.candidate, 'incremental', 2)
        self.assertEqual(r['status'], 'passed')
        self.assertEqual(r['steps'][-1]['command'], ['lake', 'build'])
        self.assertEqual(git(out / 'incremental', 'rev-parse', 'HEAD'), self.candidate)
        self.assertIsNone(r['build_cpu_reduction'])
        self.assertFalse(r['independent_verification'])
        self.assertIn('build unset 2', (out / 'candidate-build.log').read_text())

    def test_clean_pair(self):
        out = self.root / 'clean'
        r = run(self.repo, out, self.base, self.candidate, 'clean', 3)
        self.assertEqual(r['status'], 'passed')
        self.assertIsNotNone(r['build_cpu_reduction'])
        self.assertFalse(r['independent_verification'])
        self.assertIn('build false 3', (out / 'baseline-validate.log').read_text())
        self.assertIn('build false 3', (out / 'candidate-validate.log').read_text())
        self.assertEqual(git(out / 'baseline', 'rev-parse', 'HEAD'), self.base)
        self.assertEqual(git(out / 'candidate', 'rev-parse', 'HEAD'), self.candidate)

    def test_comparator_pair(self):
        out = self.root / 'comp'
        r = run(self.repo, out, self.base, self.candidate, 'comparator', 1)
        self.assertTrue(r['independent_verification'])
        self.assertIsNone(r['build_cpu_reduction'])
        self.assertIn('comparator false 1', (out / 'candidate-validate.log').read_text())

    def test_failure_report(self):
        out = self.root / 'failed'
        with patch.dict(os.environ, {'FAIL_BUILD': '1'}), self.assertRaises(RuntimeError):
            run(self.repo, out, self.base, self.candidate, 'incremental', 2)
        r = json.loads((out / 'report.json').read_text())
        self.assertEqual(r['status'], 'failed')
        self.assertEqual(r['steps'][-1]['exit'], 9)
        self.assertIsNone(r['build_cpu_reduction'])

    def test_output_guard(self):
        for out in (self.root, self.repo / 'new'):
            with self.assertRaises(ValueError):
                run(self.repo, out, self.base, self.candidate, 'incremental', 1)


if __name__ == '__main__':
    unittest.main()
