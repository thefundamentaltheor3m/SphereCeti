#!/usr/bin/env python3
"""Build the full inventory, then apply approved compiled/axiom/lint policy.

Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
scripts/{sandbox-build.sh,Axioms.lean,ModuleSystem.lean,lint-env.sh,lint-style.sh}.
Apache-2.0; TauCeti contributors. All tools and default policy are anchored to this copy.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

TRUSTED = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TRUSTED / 'scripts'))
from check_modules import BoundaryError, Module, check, source_dependencies

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
POLICY_FIELDS = {'schema_version', 'linters', 'empty_modules', 'axiom_exceptions',
                 'roadmap_admissions', 'lint_baseline', 'nolint_allowlist'}


class AuditError(ValueError):
    pass


def fields(value, expected, context):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise AuditError(f'{context}: unexpected fields')


def text(value):
    if not isinstance(value, str) or not value.strip() or any(ord(c) < 32 for c in value):
        raise AuditError('expected nonempty text without control characters')
    return value


def load_policy(path: Path) -> dict:
    policy = json.loads(path.read_text())
    fields(policy, POLICY_FIELDS, 'audit policy')
    if type(policy['schema_version']) is not int or policy['schema_version'] != 1:
        raise AuditError('unsupported audit policy version')
    linters = policy['linters']
    if not isinstance(linters, list) or not linters or linters != sorted(set(map(text, linters))):
        raise AuditError('linters must be a nonempty sorted unique list')
    for field, keys in (
        ('empty_modules', {'moduleName'}),
        ('axiom_exceptions', {'moduleName', 'name', 'axiom'}),
        ('roadmap_admissions', {'moduleName', 'name'}),
        ('lint_baseline', {'moduleName', 'name', 'linter'}),
        ('nolint_allowlist', {'moduleName', 'name', 'linter'}),
    ):
        if not isinstance(policy[field], list):
            raise AuditError(f'{field}: expected list')
        seen = set()
        for entry in policy[field]:
            fields(entry, keys | {'reason'}, field)
            for value in entry.values():
                text(value)
            key = tuple(entry[k] for k in sorted(keys))
            if key in seen:
                raise AuditError(f'{field}: duplicate exception')
            seen.add(key)
            if field == 'roadmap_admissions' and not (
                entry['moduleName'] == 'SphereCetiRoadmap' or
                entry['moduleName'].startswith('SphereCetiRoadmap.')
            ):
                raise AuditError('admission ledger entries must belong to roadmap modules')
    return policy


def key(entry, names):
    return tuple(entry[n] for n in names)


def assess(report: dict, inventory: list[dict], policy: dict) -> dict:
    fields(report, {'schema_version', 'modules', 'declarations', 'linters', 'findings', 'nolints'},
           'compiled report')
    if type(report['schema_version']) is not int or report['schema_version'] != 1:
        raise AuditError('unsupported compiled report version')
    for name in ('modules', 'declarations', 'linters', 'findings', 'nolints'):
        if not isinstance(report[name], list):
            raise AuditError(f'report {name}: expected list')
    sources = {m['name']: m for m in inventory if m['kind'] in ('library', 'roadmap')}
    seen_modules = set()
    errors, stale = [], []
    counts = dict.fromkeys(sources, 0)
    for module in report['modules']:
        fields(module, {'name', 'isModule', 'imports'}, 'compiled module')
        name = text(module['name'])
        if name not in sources or name in seen_modules:
            raise AuditError('duplicate or unexpected compiled module')
        seen_modules.add(name)
        if type(module['isModule']) is not bool or not module['isModule']:
            errors.append(f'module system: {name} did not compile with module')
        if not isinstance(module['imports'], list):
            raise AuditError('expected compiled import list')
        for imported in module['imports']:
            text(imported)
            if sources[name]['kind'] == 'library' and imported in sources and sources[imported]['kind'] != 'library':
                errors.append(f'compiled forbidden import: {name} -> {imported}')
    if seen_modules != sources.keys():
        raise AuditError('compiled module coverage differs from source inventory')
    if report['linters'] != policy['linters']:
        raise AuditError(f"default linter set drift: {report['linters']!r}")
    exceptions = {key(e, ('moduleName', 'name', 'axiom')) for e in policy['axiom_exceptions']}
    ledger = {key(e, ('moduleName', 'name')) for e in policy['roadmap_admissions']}
    used_exceptions, used_admissions, declarations = set(), set(), set()
    for decl in report['declarations']:
        fields(decl, {'moduleName', 'name', 'axioms'}, 'declaration')
        owner, name = text(decl['moduleName']), text(decl['name'])
        if owner not in sources or name in declarations:
            raise AuditError('duplicate or foreign declaration in compiled report')
        declarations.add(name)
        counts[owner] += 1
        if not isinstance(decl['axioms'], list) or decl['axioms'] != sorted(set(map(text, decl['axioms']))):
            raise AuditError('axiom dependencies must be a sorted unique list')
        for axiom in decl['axioms']:
            if axiom in ALLOWED_AXIOMS:
                continue
            triple = (owner, name, axiom)
            if sources[owner]['kind'] == 'roadmap' and axiom == 'sorryAx' and (owner, name) in ledger:
                used_admissions.add((owner, name))
            elif sources[owner]['kind'] == 'library' and triple in exceptions:
                used_exceptions.add(triple)
            else:
                errors.append(f'axioms: {owner}: {name} depends on {axiom}')
    empty = {e['moduleName'] for e in policy['empty_modules']}
    for name, count in counts.items():
        if count == 0 and name not in empty:
            errors.append(f'empty audit: {name} owns zero declarations without an approved exception')
    if ledger != used_admissions:
        errors.append(f'roadmap ledger drift: unused entries {sorted(ledger - used_admissions)!r}')
    # Fixes are visible ratchets; stale lint/axiom/empty exceptions never broaden acceptance.
    stale.extend(f'unused axiom exception: {e!r}' for e in sorted(exceptions - used_exceptions))
    stale.extend(f'unused empty-module exception: {n}' for n in sorted(empty) if counts.get(n, -1) != 0)
    for category, baseline_name in (('findings', 'lint_baseline'), ('nolints', 'nolint_allowlist')):
        baseline = {key(e, ('moduleName', 'name', 'linter')) for e in policy[baseline_name]}
        observed = set()
        for finding in report[category]:
            fields(finding, {'moduleName', 'name', 'linter', 'message'}, category)
            for value in finding.values():
                # Messages may contain multiline diagnostics; they never become policy keys.
                if not isinstance(value, str):
                    raise AuditError('finding values must be strings')
            item = key(finding, ('moduleName', 'name', 'linter'))
            if item[0] not in sources or not item[1] or not item[2]:
                raise AuditError('foreign or malformed linter finding')
            observed.add(item)
            if item not in baseline:
                errors.append(f"{category}: {' / '.join(item)}: {finding['message']}")
        stale.extend(f'unused {baseline_name}: {item!r}' for item in sorted(baseline - observed))
    return {'passed': not errors, 'errors': errors, 'ratchet': stale, 'declaration_counts': counts,
            'roadmap_admissions': len(used_admissions), 'modules': len(sources)}


def run(command, root, *, env=None, timeout=300):
    result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        raise AuditError(f"{command[0]} failed ({result.returncode}):\n{result.stdout}{result.stderr}")
    return result.stdout


def build_all(root, modules):
    # Explicit module targets include nested/unimported modules regardless of root imports/globs.
    project = [m for m in modules if m['kind'] in ('library', 'roadmap')]
    for start in range(0, len(project), 64):
        run(['lake', 'build', *('+' + m['name'] + ':olean' for m in project[start:start + 64])], root)
    # Lake does not declare libraries for audit tools or committed fixtures. Elaborate these
    # too, in import order, into the same generated search path; never execute their main.
    remaining = {m['name']: m for m in modules if m['kind'] not in ('library', 'roadmap')}
    # Direct Lean invocations do not build missing external imports. Ask Lake to prepare
    # those package source targets first, using Lean's parsed paths rather than guessed names.
    packages = (root / '.lake/packages').resolve()
    dependencies = set()
    for module in remaining.values():
        source = Module(module['name'], module['path'], module['kind'])
        dependencies.update(str(path) + ':olean' for path in source_dependencies(root, source)
                            if path.is_relative_to(packages))
    dependencies = sorted(dependencies)
    for start in range(0, len(dependencies), 64):
        run(['lake', 'build', *dependencies[start:start + 64]], root)
    while remaining:
        ready = [m for m in remaining.values() if not any(i in remaining for i in m['imports'])]
        if not ready:
            raise AuditError('cyclic tooling/fixture imports')
        for module in ready:
            output = root / '.lake/build/lib/lean' / (module['name'].replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            run(['lake', 'env', 'lean', '-o', str(output), module['path']], root)
            del remaining[module['name']]


def audit(root: Path, policy_path: Path, report_path: Path | None = None):
    policy = load_policy(policy_path)
    modules = check(root)['modules']
    build_all(root, modules)
    # Re-enter Lake's candidate environment after building. Only the approved driver runs.
    project = [{k: m[k] for k in ('name', 'path', 'kind')} for m in modules
               if m['kind'] in ('library', 'roadmap')]
    (root / '.lake').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='audit-', dir=root / '.lake') as directory:
        request, output = Path(directory) / 'request.json', Path(directory) / 'report.json'
        request.write_text(json.dumps(project))
        run(['lake', 'env', 'lean', '--run', str(TRUSTED / 'scripts/Audit.lean'),
             str(request), str(output)], root)
        report = json.loads(output.read_text())
    verdict = assess(report, modules, policy)
    if report_path:
        report_path.write_text(json.dumps({'verdict': verdict, 'compiled': report}, indent=2) + '\n')
    for reminder in verdict['ratchet']:
        print('audit ratchet: ' + reminder)
    if not verdict['passed']:
        raise AuditError('\n'.join(verdict['errors']))
    # Admission warnings are confined to roadmap targets. Library diagnostics must be silent;
    # cached replay enforces this without rebuilding or suppressing dependency diagnostics.
    library = [m for m in modules if m['kind'] == 'library']
    for start in range(0, len(library), 64):
        run(['lake', 'build', '--iofail', *('+' + m['name'] + ':olean' for m in library[start:start + 64])], root)
    print(f"compiled audits: {len(modules)} sources built; {sum(verdict['declaration_counts'].values())} "
          f"owned declarations checked; {verdict['roadmap_admissions']} ledgered roadmap admissions; OK")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--policy', type=Path, default=TRUSTED / 'policy/audits.json')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    try:
        audit(args.root.resolve(), args.policy.resolve(), args.report)
        return 0
    except (AuditError, BoundaryError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f'compiled audits: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
