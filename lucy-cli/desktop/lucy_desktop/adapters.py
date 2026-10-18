"""Documented app events only; never scrape historical transcript files."""
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys
import uuid

from .service import call


def hook(source, data):
    session = data.get('session_id') or data.get('conversation_id')
    if not session:
        return {}
    event = data.get('hook_event_name', '')
    base = dict(source=source, session=session)
    if source == 'cursor' and event == 'postToolUse':
        try:
            result = call(dict(base, op='context'))
        except ValueError:
            return {}
        return {'additional_context': result['context'] + '\nLucy conversation: ' + json.dumps(base)}
    if event in ('SessionStart', 'sessionStart', 'SessionEnd', 'sessionEnd', 'Interrupt'):
        call(dict(base, op='cancel' if event == 'Interrupt' else 'close'))
        return {}
    if event in ('UserPromptSubmit', 'beforeSubmitPrompt'):
        # Claude has no stable prompt event ID. Assign one without conflating repeated text.
        turn = data.get('turn_id') or data.get('generation_id') or str(uuid.uuid4())
        result = call(dict(base, op='prompt', text=data['prompt'], event=turn,
                           workspace=data.get('cwd') or (data.get('workspace_roots') or [str(Path.home())])[0]))
        if result.get('active'):
            context = result['context']
            context += '\nLucy conversation: ' + json.dumps(base)
            context += '\nOnly activated exchanges are saved. Use lucy memory record for commentary not exposed by response hooks.'
            if source == 'cursor':
                # Cursor's submission response cannot inject model context.
                return {'continue': True}
            return {'hookSpecificOutput': {'hookEventName': 'UserPromptSubmit', 'additionalContext': context}}
        return {}
    if event in ('Stop', 'afterAgentResponse'):
        text = data.get('last_assistant_message') if event == 'Stop' else data.get('text')
        if not isinstance(text, str) or not text:
            return {}
        active = call({'op': 'status'})['active']
        current = next((s for s in active if s['source'] == source and s['session'] == session), None)
        if not current:
            return {}
        # A supplied turn ID binds the response to its original invocation. Providers
        # without one use the active turn plus content hash, never read the transcript.
        turn = data.get('turn_id') or data.get('generation_id') or current['turn']
        digest = hashlib.sha256(text.encode()).hexdigest()
        request = dict(base, op='record', text=text, event=(turn or 'response') + ':' + digest)
        if turn:
            request['turn'] = turn
        call(request)
    return {}


def mcp(source, session):
    # No activate, approve or arbitrary execute tool is exposed to models.
    for line in sys.stdin:
        req = json.loads(line)
        if 'id' not in req:
            continue
        try:
            method = req['method']
            if method == 'initialize':
                result = {'protocolVersion': '2024-11-05', 'capabilities': {'tools': {}},
                          'serverInfo': {'name': 'nibli-lucy-memory', 'version': '1.0.0'}}
            elif method == 'tools/list':
                result = {'tools': [{'name': 'lucy_recall',
                                    'description': 'Recall private memory only in the explicitly activated Lucy conversation.',
                                    'inputSchema': {'type': 'object', 'properties': {'query': {'type': 'string'}},
                                                    'required': ['query'], 'additionalProperties': False}}]}
            elif method == 'tools/call' and req['params']['name'] == 'lucy_recall':
                result = {'content': [{'type': 'text', 'text': json.dumps(call(dict(op='recall', source=source,
                           session=session, query=req['params']['arguments']['query'])))}]}
            elif method == 'ping':
                result = {}
            else:
                raise ValueError('Unsupported method')
            response = dict(jsonrpc='2.0', id=req['id'], result=result)
        except Exception as e:
            response = dict(jsonrpc='2.0', id=req['id'], error={'code': -32000, 'message': str(e)})
        print(json.dumps(response), flush=True)


def native():
    # Browser sends only handoff/context requests after explicit interaction.
    while header := sys.stdin.buffer.read(4):
        if len(header) != 4:
            return
        length = struct.unpack('<I', header)[0]
        if length > 1024 * 1024:
            return
        raw = sys.stdin.buffer.read(length)
        if len(raw) != length:
            return
        try:
            req = json.loads(raw)
            if req.get('op') == 'handoff':
                text = str(req.get('text', ''))[:200000]
                # JSON via stdin avoids leaking selected content into process arguments.
                child = subprocess.Popen(['lucy', 'ui', '--handoff-stdin'], stdin=subprocess.PIPE,
                                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                child.stdin.write(json.dumps({'text': text, 'source': req.get('url', 'browser')}).encode())
                child.stdin.close()
                result = {'opened': True}
            elif req.get('op') == 'context':
                # One-shot explicit context preparation. Always close after the response.
                session = str(uuid.uuid4())
                base = dict(source='browser', session=session)
                try:
                    result = call(dict(base, op='prompt', text='/lucy ' + str(req.get('query', '')),
                                       event=str(uuid.uuid4()), workspace=str(Path.home())))
                finally:
                    call(dict(base, op='close'))
            else:
                raise ValueError('Unsupported browser action')
        except Exception as e:
            result = {'error': str(e)}
        out = json.dumps(result).encode()
        sys.stdout.buffer.write(struct.pack('<I', len(out)) + out)
        sys.stdout.buffer.flush()
