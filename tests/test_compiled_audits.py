"""Real rc1 compiled-environment regressions in disposable projects; no fixture proofs published."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_audits import AuditError, assess, load_policy

HEADER = '''/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

'''


class CompiledAuditsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='sphereceti-audit-fixture-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / '.lake').mkdir()
        # Trusted fixture-only sharing; candidate Git trees still reject source symlinks.
        (self.root / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
        for path in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
            (self.root / path).write_bytes((ROOT / path).read_bytes())
        self.write('SphereCeti.lean')
        self.write('SphereCetiRoadmap.lean')
        self.policy = load_policy(ROOT / 'policy/audits.json')
        # These disposable projects do not contain the installed mathematical roadmap.
        self.policy['roadmap_admissions'] = []
        self.approved_fixture_policy = copy.deepcopy(self.policy)

    def write(self, path, body='', imports='', *, module=True, header=True):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text((HEADER if header else '') + ('module\n\n' if module else '') +
                        imports + '\n' + body + '\n')

    def run_audit(self, *, custom_policy=False):
        # Select host-owned fixture policy explicitly; candidate policy is never consulted.
        policy = self.root / '.lake/approved-test-policy.json'
        policy.write_text(json.dumps(self.policy if custom_policy else self.approved_fixture_policy))
        env = os.environ.copy()
        env.update(LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false')
        result = subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/check_audits.py'),
                                 '--root', str(self.root), '--policy', str(policy),
                                 '--report', str(self.root / '.lake/report.json')],
                                cwd=self.root, env=env, capture_output=True, text=True, timeout=180)
        path = self.root / '.lake/report.json'
        report = json.loads(path.read_text()) if path.exists() else None
        return result, report

    def reject(self, fragment, **kwargs):
        result, report = self.run_audit(**kwargs)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(fragment, result.stderr, result.stderr)
        return report

    def test_unimported_nested_admission_is_rejected(self):
        self.write('SphereCeti/Unused/Hidden.lean', 'public theorem hidden : 2 = 3 := by sorry')
        report = self.reject('hidden depends on sorryAx')
        self.assertIn('SphereCeti.Unused.Hidden', report['verdict']['declaration_counts'])

    def test_new_axiom_and_definition_dependency_are_both_owned(self):
        self.write('SphereCeti/Bad.lean', '''/-- Deliberately unproved fixture value. -/
public axiom secretValue : Nat
/-- A definition must be audited just like a theorem. -/
public noncomputable def taintedValue : Nat := secretValue
/-- A transitive dependent. -/
public noncomputable def secondTaint : Nat := taintedValue
/-- Deliberately unproved fixture type. -/
public axiom secretType : Type
/-- A type dependency also counts. -/
public def typedIdentity (x : secretType) : secretType := x''')
        report = self.reject('taintedValue depends on secretValue')
        errors = '\n'.join(report['verdict']['errors'])
        self.assertIn('secretValue depends on secretValue', errors)
        self.assertIn('secondTaint depends on secretValue', errors)
        self.assertIn('typedIdentity depends on secretType', errors)

    def test_private_definition_depending_on_sorry_is_audited(self):
        self.write('SphereCeti/Private.lean', 'private def hiddenValue : Nat := by sorry')
        report = self.reject('depends on sorryAx')
        self.assertTrue(any('_private.' in d['name'] and 'sorryAx' in d['axioms']
                            for d in report['compiled']['declarations']))

    def test_foreign_namespace_does_not_hide_library_ownership(self):
        self.write('SphereCeti/Escape.lean', 'public theorem OtherProject.bad : 2 = 3 := by sorry')
        self.reject('OtherProject.bad depends on sorryAx')

    def test_native_decide_axiom_is_rejected(self):
        self.write('SphereCeti/Native.lean', 'public theorem computed : 1 + 1 = 2 := by native_decide',
                   imports='import Lean.Elab.Tactic.Decide\n')
        report = self.reject('computed depends on ')
        computed = next(d for d in report['compiled']['declarations'] if d['name'] == 'computed')
        self.assertTrue(any('._native.native_decide.' in ax for ax in computed['axioms']))

    def test_unused_roadmap_import_is_rejected_before_axiom_use(self):
        self.write('SphereCeti/BadImport.lean', imports='import SphereCetiRoadmap\n')
        self.reject('forbidden import: SphereCeti.BadImport')

    def test_compiled_module_flag_cannot_be_faked_by_a_comment(self):
        self.write('SphereCeti/Legacy.lean', '-- module\n/-- Value. -/\ndef value : Nat := 1', module=False)
        self.reject('SphereCeti.Legacy did not compile with module')

    def test_new_empty_module_needs_explicit_policy(self):
        self.write('SphereCeti/Empty.lean')
        self.reject('SphereCeti.Empty owns zero declarations')

    def test_documented_definition_passes_and_undocumented_one_fails(self):
        self.write('SphereCeti/Good.lean', '/-- Identity fixture. -/\npublic def identity (n : Nat) : Nat := n\npublic theorem choiceFixture (p : Prop) : p ∨ ¬p := Classical.em p')
        result, report = self.run_audit()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertGreater(report['verdict']['declaration_counts']['SphereCeti.Good'], 0)
        self.assertTrue(any('Classical.choice' in d['axioms'] for d in report['compiled']['declarations']))
        self.write('SphereCeti/Good.lean', 'public def identity (n : Nat) : Nat := n')
        self.reject('docString')

    def test_environment_lint_and_nolint_cannot_silence_themselves(self):
        self.write('SphereCeti/Lint.lean', '/-- Deliberately unused argument. -/\npublic def ignores (n : Nat) : Nat := 1',
                   imports='public import Mathlib.Init\n')
        self.reject('unusedArguments')
        self.write('SphereCeti/Lint.lean', '''/-- A nolint must be separately approved. -/
@[nolint unusedArguments] public def ignores (n : Nat) : Nat := 1''', imports='public import Mathlib.Init\n')
        self.reject('nolints: SphereCeti.Lint / ignores / unusedArguments')

    def test_source_header_and_text_lint_cover_unimported_modules(self):
        self.write('SphereCeti/Style.lean', '/-- Value. -/\npublic def value : Nat := 1', header=False)
        self.reject('header')
        self.write('SphereCeti/Style.lean', '/-- Value. -/\npublic def value : Nat := 1  ')
        self.reject('source-style lint rejected')
        (self.root / 'SphereCeti/Style.lean').unlink()
        self.write('SphereCeti/lowercase.lean', '/-- Value. -/\npublic def value : Nat := 1')
        self.reject('module-name lint rejected')

    def test_roadmap_ledger_is_exact_and_cannot_authorize_library_admissions(self):
        self.write('SphereCetiRoadmap/Target.lean', 'public theorem planned : 2 = 3 := by sorry')
        self.reject('planned depends on sorryAx')
        self.policy['roadmap_admissions'] = [
            {'moduleName': 'SphereCetiRoadmap.Target', 'name': 'planned', 'reason': 'Intentional fixture target.'}]
        result, report = self.run_audit(custom_policy=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(report['verdict']['roadmap_admissions'], 1)
        self.write('SphereCetiRoadmap/Target.lean', 'public theorem planned : 2 = 2 := rfl')
        self.reject('roadmap ledger drift', custom_policy=True)

    def test_candidate_policy_is_not_the_default_policy(self):
        self.write('SphereCeti/Bad.lean', 'public theorem bad : 2 = 3 := by sorry')
        (self.root / 'policy').mkdir()
        self.policy['axiom_exceptions'] = [
            {'moduleName': 'SphereCeti.Bad', 'name': 'bad', 'axiom': 'sorryAx', 'reason': 'Unapproved candidate edit.'}]
        (self.root / 'policy/audits.json').write_text(json.dumps(self.policy))
        self.reject('bad depends on sorryAx')

    def test_unimported_tooling_and_fixtures_are_elaborated(self):
        self.write('tests/fixtures/Broken.lean', 'def broken : Nat := "not a natural"')
        self.reject('Type mismatch')
        self.write('scripts/Support.lean', 'public def support : Nat := 1',
                   imports='import Mathlib.Tactic.SetNotationForOrder\n')
        self.write('tests/fixtures/Broken.lean', 'public def fixtureValue : Nat := support',
                   imports='public import scripts.Support\n')
        result, _ = self.run_audit()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('4 sources built', result.stdout)


class AuditPolicyTest(unittest.TestCase):
    def setUp(self):
        self.policy = load_policy(ROOT / 'policy/audits.json')
        # These disposable projects do not contain the installed mathematical roadmap.
        self.policy['roadmap_admissions'] = []
        self.inventory = [{'name': 'SphereCeti', 'path': 'SphereCeti.lean', 'kind': 'library'},
                          {'name': 'SphereCetiRoadmap', 'path': 'SphereCetiRoadmap.lean', 'kind': 'roadmap'}]
        self.report = {'schema_version': 1, 'modules': [{'name': m['name'], 'isModule': True,
                       'imports': []} for m in self.inventory], 'declarations': [],
                       'linters': self.policy['linters'], 'findings': [], 'nolints': []}

    def test_missing_or_duplicate_module_and_linter_drift_fail_closed(self):
        cases = []
        missing = copy.deepcopy(self.report); missing['modules'].pop(); cases.append(missing)
        duplicate = copy.deepcopy(self.report); duplicate['modules'].append(duplicate['modules'][0]); cases.append(duplicate)
        drift = copy.deepcopy(self.report); drift['linters'] = []; cases.append(drift)
        for report in cases:
            with self.subTest(report=report), self.assertRaises(AuditError):
                assess(report, self.inventory, self.policy)

    def test_compiled_import_rejection_is_independent_of_declarations(self):
        self.report['modules'][0]['imports'] = ['SphereCetiRoadmap']
        result = assess(self.report, self.inventory, self.policy)
        self.assertFalse(result['passed'])
        self.assertIn('compiled forbidden import', result['errors'][0])

    def test_exact_environment_lint_exception_and_ratchet(self):
        finding = {'moduleName': 'SphereCeti', 'name': 'foo', 'linter': 'unusedArguments', 'message': 'unused'}
        self.report['findings'] = [finding]
        self.assertFalse(assess(self.report, self.inventory, self.policy)['passed'])
        self.policy['lint_baseline'] = [{k: v for k, v in finding.items() if k != 'message'} | {'reason': 'Test.'}]
        self.assertTrue(assess(self.report, self.inventory, self.policy)['passed'])
        self.report['findings'] = []
        self.assertTrue(assess(self.report, self.inventory, self.policy)['ratchet'])

    def test_no_unreasoned_exception_or_library_admission_ledger(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'policy.json'
            self.policy['roadmap_admissions'] = [{'moduleName': 'SphereCeti', 'name': 'bad', 'reason': 'No.'}]
            path.write_text(json.dumps(self.policy))
            with self.assertRaises(AuditError):
                load_policy(path)
            self.policy['roadmap_admissions'][0]['moduleName'] = 'SphereCetiRoadmap'
            del self.policy['roadmap_admissions'][0]['reason']
            path.write_text(json.dumps(self.policy))
            with self.assertRaises(AuditError):
                load_policy(path)
