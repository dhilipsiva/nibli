// The same request snapshots as the native/Wasmtime adapters. No engine code.
const fs = require('node:fs');
const path = require('node:path');
const { Session } = require(path.resolve(process.argv[2]));
const request = JSON.parse(fs.readFileSync(process.argv[3], 'utf8'));
const session = new Session();
session.set_max_chain_depth(request.depth);
const ids = [];
for (const statement of request.statements) {
  const allocated = Array.from(session.assert_text(statement));
  if (allocated.length !== 1) throw new Error('one ID per statement required');
  ids.push(allocated[0]);
}
function certify(stage) {
  request.queries.forEach((query, index) => {
    const envelope = JSON.parse(session.certify(query));
    console.log(JSON.stringify({ stage, index, envelope }));
  });
}
certify(0);
request.updates.forEach((update, i) => {
  if (update.op === 'retract') session.retract_fact(ids[update.index]);
  else if (update.op === 'assert') ids.push(...Array.from(session.assert_text(update.text)));
  else throw new Error('reopening persistence is not a browser operation');
  certify(i + 1);
});
session.free();
