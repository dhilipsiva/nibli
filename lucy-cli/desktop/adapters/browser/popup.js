const api = globalThis.browser || globalThis.chrome;
const output = document.getElementById('result');
async function send(op) {
  try {
    let request;
    if (op === 'context') request = {op, query: document.getElementById('query').value};
    else {
      const [tab] = await api.tabs.query({active: true, currentWindow: true});
      const result = await api.scripting.executeScript({target: {tabId: tab.id},
        func: selection => selection ? window.getSelection().toString() : document.body.innerText,
        args: [op === 'selection']});
      request = {op: 'handoff', url: tab.url, text: result[0].result.slice(0, 200000)};
    }
    const response = await api.runtime.sendNativeMessage('dev.nibli.lucy', request);
    output.value = response.error || response.context || 'Opened Ask Lucy. Review the context and press Send.';
  } catch (error) { output.value = String(error); }
}
for (const op of ['selection', 'page', 'context']) document.getElementById(op).onclick = () => send(op);
