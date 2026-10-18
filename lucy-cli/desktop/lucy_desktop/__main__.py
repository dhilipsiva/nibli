import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

from . import adapters, model
from .service import call, serve


def main():
    parser = argparse.ArgumentParser(description='Nibli Lucy desktop runtime')
    sub = parser.add_subparsers(dest='command', required=True)
    daemon = sub.add_parser('serve')
    daemon.add_argument('--data', default=str(Path.home() / '.local/share/lucy'))
    daemon.add_argument('--identity', default=os.environ.get('LUCY_IDENTITY'))
    for command in ('chat', 'ui'):
        p = sub.add_parser(command)
        p.add_argument('--workspace', default=str(Path.cwd() if Path.cwd() != Path.home() else Path.home() / 'LucyTasks'))
        p.add_argument('--handoff-stdin', action='store_true')
        p.add_argument('--files', nargs='*')
    for command in ('sleep', 'memory', 'mcp'):
        p = sub.add_parser(command)
        p.add_argument('--source', required=True)
        p.add_argument('--session', required=True)
        if command == 'memory':
            p.add_argument('operation', choices=['recall', 'record', 'transcript', 'prompt'])
            p.add_argument('--text', default='')
            p.add_argument('--event')
            p.add_argument('--workspace', default=str(Path.cwd()))
            p.add_argument('--stdin', action='store_true')
    hook = sub.add_parser('desktop-hook')
    hook.add_argument('source', choices=['claude', 'codex', 'cursor'])
    sub.add_parser('native-host')
    sub.add_parser('setup-model')
    archive = sub.add_parser('archive')
    archive.add_argument('operation', choices=['import', 'reindex'])
    integration = sub.add_parser('integrations')
    integration.add_argument('operation', choices=['status', 'install'])
    integration.add_argument('--browser-id')
    args = parser.parse_args()
    if args.command == 'serve':
        serve(args.data, args.identity)
    elif args.command == 'desktop-hook':
        # Hooks are transparent when inactive; errors are visible without blocking the host.
        try:
            print(json.dumps(adapters.hook(args.source, json.load(sys.stdin))))
        except Exception as e:
            print('Lucy hook: ' + str(e), file=sys.stderr)
            print('{}')
    elif args.command == 'native-host':
        adapters.native()
    elif args.command == 'mcp':
        adapters.mcp(args.source, args.session)
    elif args.command == 'sleep':
        print(json.dumps(call(dict(op='sleep', source=args.source, session=args.session))))
    elif args.command == 'memory':
        text = sys.stdin.read() if args.stdin else args.text
        req = dict(source=args.source, session=args.session, op=args.operation)
        if args.operation == 'recall':
            req['query'] = text
        elif args.operation in ('record', 'prompt'):
            req.update(text=text, event=args.event or str(uuid.uuid4()), workspace=args.workspace)
        print(json.dumps(call(req), ensure_ascii=False))
    elif args.command == 'setup-model':
        # Explicit setup is the only runtime download path. Verify before use.
        subprocess.run(['ollama', 'pull', model.MODEL], check=True,
                       env=dict(os.environ, OLLAMA_HOST='127.0.0.1:11434'))
        model.verify_model()
        print('Pinned model verified: sha256:' + model.DIGEST)
    elif args.command == 'archive':
        messages = json.load(sys.stdin) if args.operation == 'import' else None
        if messages is not None and not isinstance(messages, list):
            raise ValueError('Import expects a JSON array of complete attributed messages')
        client = call({'op': 'open'})
        try:
            call(dict(client, op='begin-archive', workspace=str(Path.cwd())))
            print(json.dumps(call(dict(client, op=args.operation, messages=messages))))
        finally:
            call(dict(client, op='close'))
    elif args.command == 'integrations':
        from .install import install, status
        print(json.dumps(install(args.browser_id) if args.operation == 'install' else status(), indent=2))
    else:
        handoff = json.load(sys.stdin) if args.handoff_stdin else None
        if args.files:
            handoff = {'source': 'explicit file selection', 'text': '\n'.join(str(Path(p).absolute()) for p in args.files)}
        if args.command == 'ui':
            from .ui import ui
            ui(args.workspace, handoff)
            return
        client = call({'op': 'open'})
        print('Ask Lucy · ' + client['model'] + '\nSend a message to wake; /quit closes; Ctrl-C stops.')
        try:
            while True:
                try:
                    text = input('You: ')
                    if text == '/quit':
                        break
                    if not text.strip():
                        continue
                    Path(args.workspace).mkdir(parents=True, exist_ok=True)
                    result = call(dict(client, op='chat', text=text, event=str(uuid.uuid4()), workspace=args.workspace))
                    while True:
                        print(result.get('text', 'Lucy is asleep.'))
                        if not result.get('pending'):
                            break
                        for aid, action in result['pending'].items():
                            print(json.dumps({k: v for k, v in action.items() if k != 'before'}, indent=2))
                            allow = input('Approve this exact action? [y/N] ').lower() == 'y'
                            result = call(dict(client, op='approve', action=aid, allow=allow))
                except KeyboardInterrupt:
                    call(dict(client, op='cancel'))
                    print('\nStopped.')
                except ValueError as e:
                    print(str(e), file=sys.stderr)
        except EOFError:
            pass
        finally:
            call(dict(client, op='close'))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as e:
        print('Lucy: ' + str(e), file=sys.stderr)
        sys.exit(1)
