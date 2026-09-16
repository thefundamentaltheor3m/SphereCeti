"""Offline evaluation front door: cost facts, explicit shadow pairs and local human labels."""
from pathlib import Path

from .archive_store import locked, read, require, snapshot
from .evaluation import (case_from_source, cost_report, label_pair, labels, load_pair,
                         save_pair, show_pair)


def add_parser(commands):
    p = commands.add_parser('evaluation', description=__doc__)
    p.add_argument('action', choices=('costs', 'pair', 'show', 'label', 'labels'))
    p.add_argument('--source', type=Path, help='validated local archive tree; defaults to the private journal')
    p.add_argument('--operator-config', type=Path)
    p.add_argument('--prices', type=Path, help='explicit dated price snapshot; never fetched')
    p.add_argument('--as-of', help='explicit forecast date YYYY-MM-DD; default is each run start date')
    p.add_argument('--left', help='first execution UUID for pairing')
    p.add_argument('--right', help='second execution UUID for pairing')
    p.add_argument('--pair', help='immutable pair ID for show/label/labels')
    p.add_argument('--reviewer', help='self-reported local reviewer name, not GitHub identity')
    p.add_argument('--choice', choices=('A', 'B', 'tie', 'neither', 'unsure'))
    p.add_argument('--supersedes', help='current label ID, required when correcting a label')
    p.add_argument('--json', action='store_true')


def run_evaluation(args, project, prefs):
    allowed = {'costs': {'prices', 'as_of'}, 'pair': {'left', 'right'}, 'show': {'pair'},
               'label': {'pair', 'reviewer', 'choice', 'supersedes'}, 'labels': {'pair'}}
    for field in {'prices', 'as_of', 'left', 'right', 'pair', 'reviewer', 'choice', 'supersedes'}:
        require(getattr(args, field) is None or field in allowed[args.action], f'--{field} is not used by {args.action}')
    required = allowed[args.action] - {'prices', 'as_of', 'supersedes'}
    require(all(getattr(args, k) is not None for k in required), 'missing evaluation selection/label fields')
    root = Path(prefs.storage).expanduser().absolute() / project.repository.replace('/', '__')
    archive, store = root / 'archive', root / 'evaluation'
    # Snapshot under the archive lock, then release before taking the independent label lock.
    with locked(archive):
        files = snapshot(args.source if args.source else archive / 'journal')
    if args.action == 'costs':
        return cost_report(files, project.repository, price_bytes=read(args.prices) if args.prices else None, as_of=args.as_of)
    if args.action == 'pair':
        return save_pair(files, project.repository, store, args.left, args.right)
    if args.action == 'show':
        return show_pair(files, project.repository, store, args.pair)
    if args.action == 'label':
        return label_pair(files, project.repository, store, args.pair, args.reviewer, args.choice, args.supersedes)
    case = load_pair(store, args.pair)
    case_from_source(files, project.repository, case)
    with locked(store):
        current = labels(store, case, args.pair)
    return {'pair_id': args.pair, 'labels': current, 'advisory': True, 'merge_eligible': False}


def render(report, action):
    if action == 'show':
        return (f"Pair {report['pair_id']} (local human comparison; never merge evidence)\n\n"
                f"## A\n\n{report['A']}\n\n## B\n\n{report['B']}")
    if action == 'costs':
        recorded = report['totals']['recorded_usd']
        derived = report['totals']['repriced_usd']
        return (f"Observed {report['totals']['runs']} run(s) across {report['executions']} execution(s).\n"
                f"Recorded spend: ${recorded['sum_known']} known; {recorded['unknown_runs']} run(s) unknown.\n"
                f"Repriced estimate: ${derived['sum_known']} known; {derived['unknown_runs']} run(s) unknown.\n"
                "Use --json for numeric facts, coverage, and source/price digests.")
    import json
    return json.dumps(report, indent=2)
