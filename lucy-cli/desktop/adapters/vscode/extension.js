const vscode = require('vscode');
const net = require('node:net');
const path = require('node:path');
const crypto = require('node:crypto');
const active = new Set();
function rpc(req) {
  return new Promise((resolve, reject) => {
    const socket = net.connect(path.join(process.env.XDG_RUNTIME_DIR, 'lucy/service.sock'));
    let data = '';
    socket.on('connect', () => socket.write(JSON.stringify(req) + '\n'));
    socket.on('error', reject);
    socket.on('data', chunk => {
      data += chunk;
      if (data.length > 8 * 1024 * 1024) { socket.destroy(); reject(new Error('Response too large')); return; }
      if (data.includes('\n')) {
        socket.end();
        try { const value = JSON.parse(data); value.error ? reject(new Error(value.error)) : resolve(value); }
        catch (error) { reject(error); }
      }
    });
  });
}
exports.activate = context => {
  const participant = vscode.chat.createChatParticipant('nibli.lucy', async (request, history, stream, token) => {
    // Session IDs are carried only by this participant's result, never by prompt text.
    const prior = [...history.history].reverse().find(t => t instanceof vscode.ChatResponseTurn && t.participant === 'nibli.lucy');
    const session = prior?.result?.metadata?.session || crypto.randomUUID();
    const base = {source: 'vscode', session};
    if (!active.has(session)) { await rpc({...base, op: 'close'}); active.add(session); }
    if (request.command === 'sleep' || /^Lucy[,\s]+sleep[.!\s]*$/i.test(request.prompt)) {
      await rpc({...base, op: 'sleep'}); stream.markdown('I’m asleep in this conversation.');
      return {metadata: {session}};
    }
    const event = crypto.randomUUID();
    const wake = await rpc({...base, op: 'prompt', text: request.prompt, event,
      named_action: 'Ask Lucy', workspace: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath || process.env.HOME});
    const cancellation = token.onCancellationRequested(() => rpc({...base, op: 'cancel'}).catch(() => {}));
    try {
      const records = await rpc({...base, op: 'transcript'});
      const messages = [vscode.LanguageModelChatMessage.User(wake.context)];
      let budget = 18000;
      const recent = [];
      for (const record of [...records.messages].reverse()) {
        if (record.text.length > budget) break;
        budget -= record.text.length;
        recent.unshift(record.role === 'assistant' ? vscode.LanguageModelChatMessage.Assistant(record.text) : vscode.LanguageModelChatMessage.User(record.text));
      }
      messages.push(...recent);
      stream.progress(`Retrieved ${wake.memories.length} relevant memories`);
      const response = await request.model.sendRequest(messages, {}, token);
      let text = '';
      for await (const fragment of response.text) { text += fragment; stream.markdown(fragment); }
      if (!token.isCancellationRequested) await rpc({...base, op: 'record', text, event: event + ':reply', turn: event});
      return {metadata: {session}};
    } finally { cancellation.dispose(); }
  });
  // No participant detection or disambiguation contribution: @lucy is required.
  context.subscriptions.push(participant);
};
exports.deactivate = async () => { await Promise.all([...active].map(session => rpc({op: 'close', source: 'vscode', session}).catch(() => {}))); };
