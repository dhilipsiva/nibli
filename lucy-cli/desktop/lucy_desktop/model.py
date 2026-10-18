"""Fixed loopback Ollama transport; never downloads during inference."""
import http.client
import json
import socket
import threading

MODEL = 'qwen3.6:35b-a3b-q4_K_M'
DIGEST = '07d35212591fc27746f0a317c975a6d68754fb38e9053d82e25f06057af28522'
CONTEXT = 16384


def request(path, data=None, timeout=15):
    conn = http.client.HTTPConnection('127.0.0.1', 11434, timeout=timeout)
    try:
        conn.request('GET' if data is None else 'POST', path,
                     body=None if data is None else json.dumps(data),
                     headers={'Content-Type': 'application/json'})
        response = conn.getresponse()
        body = response.read(2 * 1024 * 1024)
        if response.status != 200:
            raise ValueError('Local Ollama error: ' + body.decode(errors='replace')[:1000])
        return json.loads(body)
    finally:
        conn.close()


def verify_model():
    models = request('/api/tags').get('models', [])
    model = next((m for m in models if m.get('name') == MODEL), None)
    if not model:
        raise ValueError('Local model is missing. Run lucy setup-model explicitly to download it.')
    if model.get('digest', '').removeprefix('sha256:') != DIGEST:
        raise ValueError('Local model digest differs from the pinned Qwen model. Run lucy setup-model.')


def chat(messages, cancel, tools):
    if cancel.is_set():
        raise ValueError('Request cancelled')
    verify_model()
    conn = http.client.HTTPConnection('127.0.0.1', 11434, timeout=600)
    finished = threading.Event()

    def interrupt():
        while not finished.wait(0.05):
            if cancel.is_set():
                if conn.sock:
                    try:
                        conn.sock.shutdown(socket.SHUT_RDWR)
                    except OSError:
                        pass
                conn.close()
                return

    watcher = threading.Thread(target=interrupt, daemon=True)
    watcher.start()
    try:
        body = dict(model=MODEL, messages=messages, tools=tools, stream=False,
                    think=False, keep_alive=0, options=dict(num_ctx=CONTEXT, num_predict=2048))
        conn.request('POST', '/api/chat', json.dumps(body), {'Content-Type': 'application/json'})
        response = conn.getresponse()
        raw = response.read(2 * 1024 * 1024)
        if cancel.is_set():
            raise ValueError('Request cancelled')
        if response.status != 200:
            raise ValueError('Local inference failed (check model memory/GPU contention): ' + raw.decode(errors='replace')[:1000])
        return json.loads(raw)['message']
    except (OSError, http.client.HTTPException) as e:
        if cancel.is_set():
            raise ValueError('Request cancelled') from e
        raise ValueError('Local Ollama is unavailable or could not complete this request: ' + str(e)) from e
    finally:
        finished.set()
        conn.close()
        # keep_alive=0 covers success; explicitly unload after cancellation as well.
        if cancel.is_set():
            try:
                request('/api/generate', {'model': MODEL, 'keep_alive': 0}, timeout=5)
            except (OSError, ValueError, http.client.HTTPException):
                pass
