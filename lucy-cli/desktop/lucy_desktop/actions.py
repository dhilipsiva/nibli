"""Workspace tools and explicit action proposals; models cannot approve actions."""
import difflib
import os
from pathlib import Path
import secrets
import signal
import subprocess
import time

DENIED_PARTS = {'.git', '.ssh', '.gnupg', '.aws', '.codex', '.claude', '.env'}
MUTATING = {'write', 'command', 'launch', 'window', 'screenshot', 'gui', 'privileged'}
SCHEMAS = [
    {'type': 'function', 'function': {'name': name, 'description': description,
     'parameters': {'type': 'object', 'properties': properties, 'required': required,
                    'additionalProperties': False}}}
    for name, description, properties, required in [
        ('read', 'Read a UTF-8 file in the task workspace.', {'path': {'type': 'string'}}, ['path']),
        ('search', 'Search workspace filenames and text, excluding private/configuration paths.', {'query': {'type': 'string'}}, ['query']),
        ('diagnostics', 'Read system, GPU and user-service status.', {}, []),
        ('write', 'Propose a complete file replacement. Requires user approval of its diff.',
         {'path': {'type': 'string'}, 'text': {'type': 'string'}}, ['path', 'text']),
        ('command', 'Propose argv in an offline workspace sandbox. Requires approval.',
         {'argv': {'type': 'array', 'items': {'type': 'string'}}}, ['argv']),
        ('launch', 'Propose launching an installed application by desktop ID.', {'desktop_id': {'type': 'string'}}, ['desktop_id']),
        ('window', 'List Hyprland windows or propose focusing/closing one by address.',
         {'action': {'type': 'string', 'enum': ['list', 'focus', 'close']}, 'address': {'type': 'string'}}, ['action']),
        ('screenshot', 'Propose a requested screenshot; never capture in the background.', {}, []),
        ('gui', 'Propose a single ydotool mouse/keyboard action. Absolute coordinates are physical pixels; inspect monitor scaling first.',
         {'argv': {'type': 'array', 'items': {'type': 'string'}}}, ['argv']),
        ('privileged', 'Propose a privileged diagnostic, authenticated through polkit.',
         {'operation': {'type': 'string', 'enum': ['hardware-info']}}, ['operation']),
    ]
]


def path_in_workspace(state, path):
    root = Path(state.workspace)
    target = (root / path).resolve()
    if not target.is_relative_to(root) or target == root:
        raise ValueError('Path must be a file inside the task workspace')
    relative = target.relative_to(root)
    if any(part in DENIED_PARTS or part.startswith('.env.') for part in relative.parts):
        raise ValueError('Credential/configuration paths require an explicit external workflow')
    return target


def unlocked():
    # Fail closed if login state cannot be established, including outside a session.
    try:
        sessions = subprocess.check_output(['loginctl', 'list-sessions', '--no-legend'], text=True, timeout=2)
        own = [line.split()[0] for line in sessions.splitlines() if line.split()[1] == str(os.getuid())]
        for session in own:
            props = subprocess.check_output(['loginctl', 'show-session', session, '-p', 'Active', '-p', 'LockedHint', '-p', 'Type'], text=True, timeout=2)
            if 'Active=yes' in props and 'LockedHint=no' in props and 'Type=wayland' in props:
                return True
    except (OSError, subprocess.SubprocessError, IndexError):
        pass
    return False


def run(argv, state, gui=False, timeout=30):
    if state.cancel.is_set() or (gui and not unlocked()):
        raise ValueError('Cancelled or desktop locked')
    # Output in a pipe is drained without retaining unlimited process output.
    import tempfile
    with tempfile.TemporaryFile() as output:
        environment = dict(os.environ)
        if argv[0] == 'pkexec':
            environment.pop('SHELL', None)
        proc = subprocess.Popen(argv, cwd=state.workspace, env=environment, stdout=output, stderr=subprocess.STDOUT,
                                start_new_session=True, stdin=subprocess.DEVNULL)
        started = time.monotonic()
        try:
            while proc.poll() is None:
                if state.cancel.wait(0.05) or time.monotonic() - started > timeout or (gui and not unlocked()):
                    raise ValueError('Action stopped: cancelled, locked or timed out')
            output.seek(0)
            return {'exit_code': proc.returncode, 'output': output.read(64000).decode(errors='replace')}
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()


def propose(state, name, args):
    if state.cancel.is_set():
        raise ValueError('Request cancelled')
    if name not in {s['function']['name'] for s in SCHEMAS}:
        raise ValueError('Unknown tool')
    if name not in MUTATING or (name == 'window' and args.get('action') == 'list'):
        return execute(state, name, args)
    preview = dict(tool=name, arguments=args)
    if name == 'write':
        target = path_in_workspace(state, args['path'])
        before = target.read_text() if target.exists() else ''
        preview['diff'] = ''.join(difflib.unified_diff(before.splitlines(True), args['text'].splitlines(True),
                                                      fromfile=args['path'], tofile=args['path']))
        preview['before'] = before
    if name in ('command', 'gui'):
        if not isinstance(args.get('argv'), list) or not args['argv'] or not all(isinstance(x, str) and '\0' not in x for x in args['argv']):
            raise ValueError('argv must be a non-empty string array')
    aid = secrets.token_urlsafe(16)
    state.pending[aid] = preview
    return {'pending_action': aid, 'preview': {k: v for k, v in preview.items() if k != 'before'}}


def execute(state, name, args, before=None):
    if state.cancel.is_set():
        raise ValueError('Request cancelled')
    if name == 'read':
        with path_in_workspace(state, args['path']).open() as f:
            return {'text': f.read(64000)}
    if name == 'search':
        query = args['query']
        argv = ['rg', '--fixed-strings', '--line-number', '--max-count', '10', '--max-filesize', '1M']
        for part in DENIED_PARTS:
            argv += ['--glob', '!' + part, '--glob', '!**/' + part + '/**']
        return run(argv + ['--', query, '.'], state)
    if name == 'diagnostics':
        return {label: run(argv, state) for label, argv in [
            ('system', ['uname', '-a']), ('services', ['systemctl', '--user', '--failed', '--no-pager']),
            ('gpu', ['nvidia-smi', '--query-gpu=name,memory.total,memory.used', '--format=csv'])]}
    if name == 'write':
        target = path_in_workspace(state, args['path'])
        now = target.read_text() if target.exists() else ''
        if now != before:
            raise ValueError('File changed since preview; request a new action')
        # Parent creation is deliberate and remains inside the resolved workspace.
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(args['text'])
        return {'written': str(target)}
    if name == 'command':
        # No host home, network, credentials, root privileges or live deployment.
        argv = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session',
                '--ro-bind', '/nix/store', '/nix/store', '--proc', '/proc', '--dev', '/dev',
                '--tmpfs', '/tmp', '--dir', '/etc', '--dir', '/run', '--dir', '/home',
                '--ro-bind', '/run/current-system/sw', '/run/current-system/sw',
                '--bind', state.workspace, state.workspace, '--chdir', state.workspace,
                '--clearenv', '--setenv', 'PATH', os.environ.get('LUCY_COMMAND_PATH', '/run/current-system/sw/bin'),
                '--setenv', 'HOME', '/tmp', '--']
        return run(argv + args['argv'], state, timeout=120)
    if name == 'launch':
        desktop_id = args['desktop_id']
        if '/' in desktop_id or desktop_id.startswith('-'):
            raise ValueError('Expected an installed desktop ID')
        return run(['gtk-launch', desktop_id], state, gui=True)
    if name == 'window':
        action = args['action']
        if action == 'list':
            return run(['hyprctl', '-j', 'clients'], state, gui=True)
        import re
        address = args.get('address', '')
        if not re.fullmatch(r'0x[0-9a-fA-F]+', address) or action not in ('focus', 'close'):
            raise ValueError('Invalid window address/action')
        dispatch = 'focuswindow' if action == 'focus' else 'closewindow'
        return run(['hyprctl', 'dispatch', dispatch, 'address:' + address], state, gui=True)
    if name == 'screenshot':
        destination = Path(os.environ['XDG_RUNTIME_DIR']) / 'lucy' / ('capture-' + secrets.token_hex(8) + '.png')
        result = run(['grim', str(destination)], state, gui=True)
        if result['exit_code']:
            raise ValueError(result['output'])
        return {'path': str(destination), 'monitors': run(['hyprctl', '-j', 'monitors'], state, gui=True)}
    if name == 'gui':
        argv = args['argv']
        if argv[0] not in ('mousemove', 'click', 'type', 'key'):
            raise ValueError('Only one mousemove/click/type/key action is supported')
        result = run(['pkexec', os.environ['LUCY_INPUT_HELPER']], state, gui=True)
        if result['exit_code']:
            raise ValueError('Input helper authentication failed')
        try:
            return run(['ydotool', *argv], state, gui=True, timeout=10)
        finally:
            # Removing the virtual device also releases held keys after cancellation.
            subprocess.run(['systemctl', 'stop', 'lucy-input.service'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5)
    if name == 'privileged' and args.get('operation') == 'hardware-info':
        return run(['pkexec', os.environ['LUCY_DMI_HELPER']], state, gui=True)
    raise ValueError('Unsupported action')
