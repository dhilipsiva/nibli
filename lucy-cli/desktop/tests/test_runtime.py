import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

from lucy_desktop import actions, adapters, model
from lucy_desktop.core import Core, addressed
from lucy_desktop.memory import Memory
from lucy_desktop.service import Service


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.core = Core(self.root / 'private')
        self.service = Service(self.root / 'service-memory')
        self.client = self.service.dispatch({'op': 'open'})

    def prompt(self, text, session='one', event='turn-1'):
        return self.core.prompt('test', session, text, event, str(self.root))

    def test_inactive_boundary_and_quotations(self):
        for text in ['hello', 'ask Lucy later', '"Lucy, hello"', '> Lucy help', '`Lucy`',
                     '```\nLucy help\n```', '<text>Lucy help</text>', 'Lucky hello', 'Lucyish',
                     '/lucy-file', '@lucy.example', 'Explain "Lucy, wake"', 'Lucy said hello', 'Lucy is a name']:
            with self.subTest(text=text):
                self.assertFalse(addressed(text))
                self.assertFalse(self.prompt(text)['active'])
        self.assertFalse((self.root / 'private').exists())
        self.assertIsNone(self.core.memory.db)

    def test_sessions_sleep_cancel_resume_and_restart(self):
        self.assertTrue(self.prompt('Lucy, hello')['active'])
        self.assertFalse(self.prompt('ordinary', session='two')['active'])
        self.assertTrue(self.prompt('follow up', event='2')['active'])
        self.core.stop('test', 'one')
        with self.assertRaises(ValueError):
            self.core.reply('test', 'one', 'late reply', 'late')
        self.assertTrue(self.prompt('resume', event='3')['active'])
        self.assertFalse(self.prompt('Lucy, sleep', event='4')['active'])
        self.assertFalse(self.prompt('ordinary again', event='5')['active'])
        restarted = Core(self.root / 'private')
        self.assertFalse(restarted.prompt('test', 'one', 'hello', '6', str(self.root))['active'])
        self.assertIsNone(restarted.memory.db)

    def test_lossless_idempotency_conflicts_and_rebuild(self):
        text = 'Lucy, café\n\n  exact 😀\t\r\n'
        first = self.prompt(text)
        self.prompt(text)
        self.assertEqual(len(self.core.memory.transcript('test', 'one')), 1)
        self.assertEqual(self.core.memory.transcript('test', 'one')[0]['text'], text)
        with self.assertRaises(ValueError):
            self.prompt('Lucy, changed')
        self.core.reply('test', 'one', 'café response', 'reply-1')
        self.core.memory.rebuild()
        result = self.core.memory.search('café', first['record_id'])
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0]['role'], 'assistant')
        self.assertEqual((self.root / 'private').stat().st_mode & 0o777, 0o700)

    def test_reject_repository_store_and_symlink(self):
        repo = self.root / 'repo'
        repo.mkdir()
        (repo / 'flake.nix').touch()
        with self.assertRaises(ValueError):
            Memory(repo / 'lucy')
        with self.assertRaises(ValueError):
            Memory('/nix/store/private')
        (self.root / 'link').symlink_to(repo, target_is_directory=True)
        with self.assertRaises(ValueError):
            Memory(self.root / 'link' / 'private')

    def test_workspace_escape_and_changed_file_before_approval(self):
        workspace = self.root / 'work'
        workspace.mkdir()
        self.core.prompt('test', 'one', 'Lucy, edit', '1', str(workspace))
        state = self.core.active('test', 'one')
        (workspace / 'escape').symlink_to(self.root / 'outside')
        for path in ('../outside', 'escape', '.ssh/id_rsa', '.env'):
            with self.subTest(path=path), self.assertRaises(ValueError):
                actions.path_in_workspace(state, path)
        result = actions.propose(state, 'write', {'path': 'file.txt', 'text': 'new'})
        self.assertFalse((workspace / 'file.txt').exists())
        (workspace / 'file.txt').write_text('changed')
        with self.assertRaises(ValueError):
            actions.execute(state, 'write', {'path': 'file.txt', 'text': 'new'}, '')
        self.assertIn(result['pending_action'], state.pending)
        self.core.stop('test', 'one')
        self.assertEqual(state.pending, {})

    def test_open_and_unaddressed_do_not_infer(self):
        with patch('lucy_desktop.model.chat', side_effect=AssertionError('inference')):
            self.service.dispatch(dict(op='prompt', source='codex', session='a', text='ordinary',
                                       event='1', workspace=str(self.root)))
        self.assertFalse((self.root / 'service-memory').exists())

    def test_local_chat_and_control_authority(self):
        with patch('lucy_desktop.model.chat', return_value={'role': 'assistant', 'content': 'reply'}) as chat:
            result = self.service.dispatch(dict(self.client, op='chat', text='hello', event='1', workspace=str(self.root)))
        self.assertEqual(result['text'], 'reply')
        self.assertEqual(chat.call_count, 1)
        req = dict(self.client, op='tool', name='write', arguments={'path': 'new.txt', 'text': 'new'})
        pending = self.service.dispatch(req)['pending_action']
        with self.assertRaises(ValueError):
            self.service.dispatch(dict(req, op='approve', action=pending, allow=True, control='model-output'))
        self.assertFalse((self.root / 'new.txt').exists())
        self.service.dispatch(dict(self.client, op='approve', action=pending, allow=True, **{'continue': False}))
        self.assertEqual((self.root / 'new.txt').read_text(), 'new')

    def test_cancel_interrupts_command_and_locked_gui(self):
        self.prompt('Lucy, command')
        state = self.core.active('test', 'one')
        with patch('lucy_desktop.actions.unlocked', return_value=False), self.assertRaises(ValueError):
            actions.run(['true'], state, gui=True)
        timer = threading.Timer(0.1, state.cancel.set)
        timer.start()
        try:
            with self.assertRaises(ValueError):
                actions.run(['sleep', '20'], state)
        finally:
            timer.cancel()

    def test_hook_contracts_and_stale_events(self):
        def transport(req):
            return self.service.dispatch(req)
        with patch('lucy_desktop.adapters.call', side_effect=transport):
            for source, event, sid in [('codex', 'UserPromptSubmit', 'session_id'),
                                       ('claude', 'UserPromptSubmit', 'session_id'),
                                       ('cursor', 'beforeSubmitPrompt', 'conversation_id')]:
                payload = {sid: source, 'hook_event_name': event, 'prompt': 'Lucy, coffee',
                           'cwd': str(self.root), 'turn_id': '1', 'generation_id': '1'}
                result = adapters.hook(source, payload)
                self.assertTrue(result.get('continue') if source == 'cursor' else result.get('hookSpecificOutput'))
                if source == 'cursor':
                    context = adapters.hook(source, {sid: source, 'hook_event_name': 'postToolUse'})
                    self.assertIn('You are Lucy D', context['additional_context'])
                    self.assertIn('cursor', context['additional_context'])
                    self.assertEqual(adapters.hook(source, {sid: 'uninvoked', 'hook_event_name': 'postToolUse'}), {})
                response = {sid: source, 'hook_event_name': 'afterAgentResponse' if source == 'cursor' else 'Stop',
                            'text': 'coffee response', 'last_assistant_message': 'coffee response',
                            'turn_id': '1', 'generation_id': '1'}
                adapters.hook(source, response)
                adapters.hook(source, response)
                self.assertEqual(len(self.service.core.memory.transcript(source, source)), 2)
                adapters.hook(source, {sid: source, 'hook_event_name': 'SessionEnd'})
                adapters.hook(source, response)
                self.assertEqual(len(self.service.core.memory.transcript(source, source)), 2)

    def test_missing_model_and_digest_mismatch_are_local_errors(self):
        for models in ([], [{'name': model.MODEL, 'digest': 'wrong'}]):
            with patch('lucy_desktop.model.request', return_value={'models': models}), self.assertRaises(ValueError):
                model.verify_model()
        with patch('lucy_desktop.model.request', return_value={'models': [{'name': model.MODEL, 'digest': model.DIGEST}]}):
            model.verify_model()

    def test_browser_permissions_and_vscode_no_detection(self):
        adapters_dir = Path(__file__).parents[1] / 'adapters'
        manifest = json.loads((adapters_dir / 'browser/manifest.json').read_text())
        self.assertEqual(set(manifest['permissions']), {'activeTab', 'scripting', 'nativeMessaging'})
        self.assertNotIn('host_permissions', manifest)
        vscode = json.loads((adapters_dir / 'vscode/package.json').read_text())
        participant = vscode['contributes']['chatParticipants'][0]
        self.assertTrue(participant['isSticky'])
        self.assertNotIn('disambiguation', participant)


    def test_settings_merge_preserves_models_and_credentials(self):
        from lucy_desktop.install import merge
        path = self.root / 'settings.json'
        original = {'model': 'selected-cloud-model', 'env': {'AUTH_PLACEHOLDER': 'fixture-only'},
                    'hooks': {'Stop': [{'hooks': [{'type': 'command', 'command': 'existing-hook'}]}]}}
        path.write_text(json.dumps(original))
        new = {'hooks': {'Stop': [{'hooks': [{'type': 'command', 'command': 'lucy desktop-hook codex'}]}]}}
        merge(path, new)
        first = path.read_text()
        merge(path, new)
        self.assertEqual(path.read_text(), first)
        saved = json.loads(first)
        self.assertEqual(saved['model'], original['model'])
        self.assertEqual(saved['env'], original['env'])
        self.assertEqual(len(saved['hooks']['Stop']), 2)
        self.assertEqual(len(list(self.root.glob('settings.json.lucy-backup-*'))), 1)

    def test_http_transport_is_local_and_unloads(self):
        import http.server
        import socketserver
        import http.client
        captured = []
        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass
            def do_GET(self):
                body = json.dumps({'models': [{'name': model.MODEL, 'digest': model.DIGEST}]}).encode()
                self.send_response(200)
                self.end_headers()
                self.wfile.write(body)
            def do_POST(self):
                body = json.loads(self.rfile.read(int(self.headers['Content-Length'])))
                captured.append(body)
                self.send_response(200)
                self.end_headers()
                self.wfile.write(b'{"message":{"role":"assistant","content":"offline fixture"}}')
        with socketserver.TCPServer(('127.0.0.1', 0), Handler) as server:
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            real = http.client.HTTPConnection
            def connection(host, port, **kwargs):
                self.assertEqual((host, port), ('127.0.0.1', 11434))
                return real('127.0.0.1', server.server_address[1], **kwargs)
            try:
                with patch('lucy_desktop.model.http.client.HTTPConnection', side_effect=connection):
                    result = model.chat([{'role': 'user', 'content': 'fixture'}], threading.Event(), [])
                self.assertEqual(result['content'], 'offline fixture')
                self.assertEqual(captured[0]['keep_alive'], 0)
                self.assertEqual(captured[0]['options']['num_ctx'], 16384)
                self.assertEqual(captured[0]['model'], model.MODEL)
            finally:
                server.shutdown()
                thread.join()

    def test_closing_one_session_cannot_record_a_late_reply(self):
        prompt = dict(op='prompt', source='test', session='one', text='Lucy, first', event='turn-1', workspace=str(self.root))
        self.service.dispatch(prompt)
        self.service.dispatch(dict(op='close', source='test', session='one'))
        self.service.dispatch(dict(prompt, text='Lucy, second', event='new'))
        with self.assertRaises(ValueError):
            self.service.dispatch(dict(op='record', source='test', session='one', text='late', event='old', turn='turn-1'))


if __name__ == '__main__':
    unittest.main()
