"""Native GTK4 chat. Opening it creates no conversation record or inference."""
import json
from pathlib import Path
import threading
import uuid

from .service import call


def ui(workspace, handoff=None):
    import gi
    gi.require_version('Gtk', '4.0')
    from gi.repository import GLib, Gtk

    client = call({'op': 'open'})
    app = Gtk.Application(application_id='dev.nibli.Lucy', flags=0)

    def activate(app):
        window = Gtk.ApplicationWindow(application=app, title='Ask Lucy')
        window.set_default_size(800, 700)
        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        box.set_margin_top(16)
        box.set_margin_bottom(16)
        box.set_margin_start(16)
        box.set_margin_end(16)
        window.set_child(box)
        status = Gtk.Label(label='Asleep · ' + client['model'], xalign=0)
        box.append(status)
        transcript = Gtk.TextView(editable=False, wrap_mode=Gtk.WrapMode.WORD_CHAR)
        scroll = Gtk.ScrolledWindow(vexpand=True)
        scroll.set_child(transcript)
        box.append(scroll)
        memories = Gtk.Label(label='No memories loaded', xalign=0, wrap=True)
        box.append(memories)
        pending = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
        box.append(pending)
        entry = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD_CHAR)
        entry.set_size_request(-1, 90)
        box.append(entry)
        if handoff:
            entry.get_buffer().set_text('Lucy, help with this context.\nSource: ' + handoff.get('source', '') + '\n\n' + handoff['text'])
        row = Gtk.Box(spacing=8)
        box.append(row)
        send, stop, sleep = (Gtk.Button(label=label) for label in ('Send', 'Stop', 'Lucy, sleep'))
        for button in (send, stop, sleep):
            row.append(button)

        def append(text):
            buf = transcript.get_buffer()
            buf.insert(buf.get_end_iter(), text + '\n\n')

        def clear_pending():
            while child := pending.get_first_child():
                pending.remove(child)

        def finished(result, error):
            send.set_sensitive(True)
            clear_pending()
            if error:
                status.set_text('Stopped · ' + str(error))
                return False
            status.set_text(('Active · ' if result.get('active') else 'Asleep · ') + client['model'])
            if result.get('text'):
                append('Lucy: ' + result['text'])
            memories.set_text('Retrieved memories:\n' + '\n'.join(
                m['source'] + ' / ' + m['id'][:12] + ': ' + m['excerpt'] for m in result.get('memories', [])))
            for aid, action in result.get('pending', {}).items():
                view = Gtk.TextView(editable=False, wrap_mode=Gtk.WrapMode.WORD_CHAR)
                preview = {k: v for k, v in action.items() if k != 'before'}
                view.get_buffer().set_text(json.dumps(preview, indent=2, ensure_ascii=False))
                action_scroll = Gtk.ScrolledWindow(min_content_height=150, max_content_height=250)
                action_scroll.set_child(view)
                pending.append(action_scroll)
                for label, allow in (('Approve this action', True), ('Deny', False)):
                    button = Gtk.Button(label=label)
                    button.connect('clicked', lambda _, a=aid, yes=allow: work(dict(op='approve', action=a, allow=yes)))
                    pending.append(button)
            return False

        def work(request):
            send.set_sensitive(False)
            clear_pending()
            status.set_text('Working · ' + client['model'])
            def run():
                try:
                    result, error = call(dict(client, **request)), None
                except Exception as e:
                    result, error = {}, e
                GLib.idle_add(finished, result, error)
            threading.Thread(target=run, daemon=True).start()

        def submit(_):
            buf = entry.get_buffer()
            text = buf.get_text(buf.get_start_iter(), buf.get_end_iter(), True)
            if not text.strip():
                return
            Path(workspace).mkdir(parents=True, exist_ok=True)
            append('You: ' + text)
            buf.set_text('')
            work(dict(op='chat', text=text, event=str(uuid.uuid4()), workspace=workspace))

        def end(op):
            try:
                call(dict(client, op=op))
            except Exception as e:
                status.set_text(str(e))
            clear_pending()
            status.set_text('Asleep' if op != 'cancel' else 'Stopped')

        send.connect('clicked', submit)
        stop.connect('clicked', lambda _: end('cancel'))
        sleep.connect('clicked', lambda _: end('sleep'))
        window.connect('close-request', lambda _: end('close'))
        window.present()

    app.connect('activate', activate)
    app.run([])
