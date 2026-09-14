"""Provider-free local archive commands and explicitly gated same-repository publication."""
from pathlib import Path

from .archive_store import enqueue, locked, rebuild, require, snapshot, validate
from .archive_sync import GitHubArchive, parse_archive_policy, sync
from .config import parse_policy, resource_text


def add_parser(commands):
    parser = commands.add_parser('archive', description=__doc__)
    parser.add_argument('action', choices=('enqueue', 'preview', 'sync', 'rebuild'))
    parser.add_argument('--operator-config', type=Path)
    parser.add_argument('--output', type=Path, help='completed review output for enqueue; new SQLite path for rebuild')
    parser.add_argument('--source', type=Path, help='local archive data tree to rebuild; default is local journal')
    parser.add_argument('--include-text', action='store_true', help='enqueue redacted rendered review prose explicitly')
    parser.add_argument('--apply', action='store_true', help='sync only: require approved main policy before remote writes')
    parser.add_argument('--json', action='store_true')


def run_archive(args, project, prefs):
    require(not args.apply or args.action == 'sync', '--apply is only for sync')
    require(not args.include_text or args.action == 'enqueue', '--include-text is only for enqueue')
    require(args.source is None or args.action == 'rebuild', '--source is only for rebuild')
    require((args.output is not None) == (args.action in ('enqueue', 'rebuild')), 'enqueue/rebuild require --output only')
    store = Path(prefs.storage).expanduser().absolute() / project.repository.replace('/', '__') / 'archive'
    if args.action == 'enqueue':
        return enqueue(args.output, store, project.repository, include_text=args.include_text)
    if args.action == 'rebuild':
        source = args.source.absolute() if args.source else store / 'journal'
        output = args.output.absolute()
        require(not output.is_relative_to(source) and not output.is_relative_to(store),
                'SQLite must stay outside archive and state directories')
        with locked(store):
            return rebuild(snapshot(source), project.repository, output)
    if args.action == 'sync' and args.apply:
        policy = parse_archive_policy(resource_text('archive.toml'))
        require(policy['enabled'] and parse_policy(resource_text('automation.toml')).posting,
                'archive publication is disabled; no network request was made')
        transport = GitHubArchive(project)
        transport.authorize()
        return sync(store, project.repository, transport)
    with locked(store):
        files = snapshot(store / 'outbox') if (store / 'outbox').exists() else {}
        records = validate(files, project.repository)
    return {'state': 'preview', 'files': len(files), 'records': len(records), 'bytes': sum(map(len, files.values())),
            'text_blobs': sum(n.startswith('blobs/') for n in files), 'publication': 'not_requested',
            'repository': project.repository, 'branch': project.archive_branch}
