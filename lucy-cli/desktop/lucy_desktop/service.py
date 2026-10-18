"""A user-owned Unix socket service. No TCP listener and no startup model access."""
import json
import os
from pathlib import Path
import secrets
import socket
import socketserver
import struct
import threading

from . import actions, model
from .core import Core

MAX_FRAME = 8 * 1024 * 1024


def socket_path():
    return str(Path(os.environ['XDG_RUNTIME_DIR']) / 'lucy' / 'service.sock')


def call(request):
    with socket.socket(socket.AF_UNIX) as sock:
        sock.settimeout(660)
        sock.connect(socket_path())
        sock.sendall(json.dumps(request, ensure_ascii=False).encode() + b'\n')
        response = sock.makefile('rb').readline(MAX_FRAME + 1)
    if len(response) > MAX_FRAME:
        raise ValueError('Response too large')
    result = json.loads(response)
    if 'error' in result:
        raise ValueError(result['error'])
    return result


class Service:
    def __init__(self, root, identity=None):
        self.core = Core(root, identity)
        self.clients = {}
        self.inference = threading.Lock()

    def controlled(self, req):
        source, session = req['source'], req['session']
        token = self.clients.get((source, session))
        if not token or not secrets.compare_digest(token, req.get('control', '')):
            raise ValueError('Only this conversation’s local UI can authorize this action')
        return source, session

    def dispatch(self, req):
        op = req['op']
        if op == 'open':
            source, session, token = 'local', secrets.token_urlsafe(24), secrets.token_urlsafe(32)
            self.clients[(source, session)] = token
            return dict(source=source, session=session, control=token, model=model.MODEL)
        if op == 'status':
            with self.core.lock:
                return {'active': [dict(source=s.source, session=s.id, turn=s.turn, pending=len(s.pending), busy=s.busy)
                                   for s in self.core.sessions.values()], 'model': model.MODEL}
        source, session = req['source'], req['session']
        if op in ('close', 'cancel', 'sleep', 'start'):
            if op == 'close':
                self.clients.pop((source, session), None)
            return self.core.stop(source, session, close=op != 'cancel')
        if op in ('prompt', 'chat'):
            if op == 'chat':
                self.controlled(req)
            explicit = False
            if req.get('control'):
                self.controlled(req)
                explicit = op == 'chat'  # Send in the named desktop chat is the wake boundary.
            if source == 'vscode' and req.get('named_action') == 'Ask Lucy':
                explicit = True
            result = self.core.prompt(source, session, req['text'], req['event'], req['workspace'], explicit)
            if op != 'chat' or not result['active']:
                return result
            self.controlled(req)
            state = self.core.active(source, session)
            with self.core.lock:
                records = self.core.memory.transcript(source, session)
                recent, size = [], 0
                for record in reversed(records):
                    if size + len(record['text']) > 18000:
                        break
                    recent.insert(0, {'role': record['role'], 'content': record['text']})
                    size += len(record['text'])
                state.messages = [{'role': 'system', 'content': result['context']}, *recent]
            return self.respond(state)
        with self.core.lock:
            state = self.core.active(source, session)
            if state.cancel.is_set():
                raise ValueError('Request cancelled')
            if op == 'record':
                if req.get('turn', state.turn) != state.turn:
                    raise ValueError('Response belongs to an earlier or cancelled turn')
                self.core.reply(source, session, req['text'], req['event'], req.get('channel', 'final'))
                return {'recorded': True}
            if op == 'recall':
                return {'memories': self.core.memory.search(req['query'])}
            if op == 'transcript':
                return {'messages': self.core.memory.transcript(source, session)}
            if op == 'reindex':
                self.controlled(req)
                self.core.memory.rebuild()
                return {'rebuilt': True}
            if op == 'import':
                self.controlled(req)
                records = req['messages']
                for record in records:
                    # Explicit import retains source/session/ID and original timestamp.
                    self.core.memory.record(record)
                return {'imported': len(records)}
            if op == 'tool':
                return actions.propose(state, req['name'], req['arguments'])
            if op == 'pending':
                self.controlled(req)
                return {'actions': state.pending}
            if op == 'approve':
                self.controlled(req)
                proposal = state.pending.pop(req['action'])
            else:
                raise ValueError('Unsupported operation')
        # Never hold the core lock across commands, authentication or inference.
        if req.get('allow'):
            result = actions.execute(state, proposal['tool'], proposal['arguments'], proposal.get('before'))
        else:
            result = {'denied': True}
        if state.messages and state.messages[-1]['role'] == 'tool':
            state.messages[-1]['content'] = json.dumps(result)
        if req.get('continue', True):
            return self.respond(state)
        return result

    def respond(self, state):
        if not self.inference.acquire(blocking=False):
            raise ValueError('Another local request is running; stop it or retry when it finishes')
        with self.core.lock:
            if self.core.sessions.get((state.source, state.id)) is not state or state.cancel.is_set():
                self.inference.release()
                raise ValueError('Conversation ended')
            state.busy = True
        try:
            for _ in range(8):
                reply = model.chat(state.messages, state.cancel, actions.SCHEMAS)
                # Do not retain hidden chain-of-thought, even if the provider returns it.
                reply.pop('thinking', None)
                state.messages.append(reply)
                calls = reply.get('tool_calls', [])
                text = reply.get('content', '')
                if text:
                    self.core.reply(state.source, state.id, text,
                                    state.turn + ':reply:' + str(len(state.messages)),
                                    'commentary' if calls else 'final')
                if not calls:
                    return dict(active=True, text=text, memories=state.memories, pending=state.pending)
                # Execute at most one proposed action per model round, so approval is exact.
                if len(calls) != 1:
                    raise ValueError('Model proposed multiple tools at once; ask for one step at a time')
                function = calls[0]['function']
                result = actions.propose(state, function['name'], function.get('arguments', {}))
                state.messages.append(dict(role='tool', tool_name=function['name'], content=json.dumps(result)))
                if state.pending:
                    return dict(active=True, text=text or 'Please review the proposed action.',
                                memories=state.memories, pending=state.pending)
            raise ValueError('Task reached its step limit; send another message to continue')
        finally:
            with self.core.lock:
                state.busy = False
            self.inference.release()


def serve(root, identity):
    os.umask(0o077)
    path = Path(socket_path())
    path.parent.mkdir(mode=0o700, exist_ok=True)
    service = Service(root, identity)

    class Handler(socketserver.StreamRequestHandler):
        def handle(self):
            pid, uid, gid = struct.unpack('3i', self.request.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
            if uid != os.getuid():
                return
            self.request.settimeout(10)
            raw = self.rfile.readline(MAX_FRAME + 1)
            try:
                if len(raw) > MAX_FRAME:
                    raise ValueError('Request too large')
                result = service.dispatch(json.loads(raw))
            except Exception as error:
                # Never log request bodies, file contents, memory or credentials.
                result = {'error': str(error)}
            try:
                self.wfile.write(json.dumps(result, ensure_ascii=False).encode() + b'\n')
            except (BrokenPipeError, ConnectionResetError):
                pass

    class Server(socketserver.ThreadingUnixStreamServer):
        daemon_threads = True

    if path.exists():
        # Do not replace a live service owned by a previous invocation.
        with socket.socket(socket.AF_UNIX) as probe:
            try:
                probe.connect(str(path))
            except ConnectionRefusedError:
                path.unlink()
            else:
                raise ValueError('Lucy service is already running')
    with Server(str(path), Handler) as server:
        os.chmod(path, 0o600)
        try:
            server.serve_forever()
        finally:
            for state in service.core.sessions.values():
                state.cancel.set()
            path.unlink(missing_ok=True)
