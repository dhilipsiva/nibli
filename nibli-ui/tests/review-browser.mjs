/** Real bundled-WASM review/admission regressions.
 * Build: nix develop --command dx build --platform web (from nibli-ui).
 * Run: node nibli-ui/tests/review-browser.mjs
 * Optional: PLAYWRIGHT_MODULE=/absolute/playwright/index.mjs,
 * BROWSER_EXECUTABLE=/path/to/chromium, NIBLI_UI_PUBLIC=/path/to/built/public.
 */
import assert from 'node:assert/strict';
import {createServer} from 'node:http';
import {readFile, mkdir} from 'node:fs/promises';
import {resolve, extname} from 'node:path';
import {fileURLToPath} from 'node:url';
const {chromium} = await import(process.env.PLAYWRIGHT_MODULE || 'playwright');
const root = resolve(fileURLToPath(new URL('../../target/dx/nibli-ui/debug/web/public', import.meta.url)));
const publicDir = process.env.NIBLI_UI_PUBLIC || root;
const mime = {'.html':'text/html', '.js':'text/javascript', '.wasm':'application/wasm', '.css':'text/css'};
const server = createServer(async (req,res)=>{
  const relative = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
  const path = resolve(publicDir, '.' + (relative === '/' ? '/index.html' : relative));
  if (!path.startsWith(publicDir + '/')) {res.writeHead(403).end();return;}
  try { const data = await readFile(path); res.writeHead(200, {'content-type':mime[extname(path)]||'application/octet-stream'}).end(data); }
  catch {res.writeHead(404).end();}
});
await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
const base = `http://127.0.0.1:${server.address().port}`;
const browser = await chromium.launch({headless:true, executablePath:process.env.BROWSER_EXECUTABLE});
const page = await browser.newPage({viewport:{width:1440,height:1000}});
page.setDefaultTimeout(10000);
const errors=[]; page.on('pageerror', e=>errors.push(String(e)));
const checks=[];
const expectText = async (locator, text)=>{await locator.filter({hasText:text}).first().waitFor();};
const top=page.locator('.main-row .col-tabs');
const query=page.locator('.query-row .col-tabs');
const output=page.locator('.output-entry');
const topTab=async name=>top.getByRole('button',{name:name==='nibli KR'? /^nibli KR/ : name,exact:name!=='nibli KR'}).click();
const qTab=async name=>query.getByRole('button',{name:name==='nibli KR'? /^nibli KR/ : name,exact:name!=='nibli KR'}).click();
const kb=()=>page.locator('#kb-kr-editor');
const qInput=()=>page.locator('#query-input');
const approve=async()=>{await topTab('Back-translation');await top.getByRole('button',{name:'Use reviewed encoding',exact:true}).click();};
const run=async()=>query.getByRole('button',{name:'Query',exact:true}).click();
const result=async text=>{await expectText(page.locator('.output-result'),text);};
try {
  await page.goto(base);
  await page.locator('.app-shell').waitFor();
  await run(); await expectText(query.locator('.translate-error'),'Use reviewed encoding'); assert.equal(await output.count(),0);
  await qInput().press('Enter'); assert.equal(await output.count(),0); checks.push('button and Enter reject unreviewed KB');
  await approve(); await run(); await result('TRUE'); checks.push('reviewed complete KB permits reasoning');
  await topTab('Source');const source=top.locator('textarea');const original=await source.inputValue();
  await source.fill(original+' ');await source.fill(original);await run();assert.equal(await output.count(),0);checks.push('source edit/revert clears prior results and approval');
  await topTab('nibli KR');await kb().fill('dog(Rex).\ninvalid syntax here\ncat(Bel).');await approve();
  await expectText(top.locator('.translate-error'),'KB not loaded: line 2');assert.equal(await output.count(),0);checks.push('middle-line error blocks whole candidate');
  await topTab('nibli KR');await kb().fill('# no assertions\n');await approve();await expectText(top.locator('.kb-status-summary'),'Empty KB loaded');
  await qInput().fill('dog(Rex).');await run();await result('FALSE');checks.push('comment-only KB admitted and explicitly empty');
  await topTab('Source');await top.locator('textarea').fill('');await topTab('nibli KR');await kb().fill('dog(Rex).');await approve();
  await expectText(top.locator('.query-hint'),'Reviewed encoding ready');await run();await result('TRUE');
  await qTab('Source');await query.locator('textarea').fill('Rex is a dog.');await qTab('nibli KR');await run();
  await expectText(query.locator('.translate-error'),'Use reviewed query');assert.equal(await output.count(),0);
  await query.getByRole('button',{name:'Use reviewed query',exact:true}).click();await run();await result('TRUE');
  await qTab('Source');await query.locator('textarea').fill('Rex is a dog. ');await query.locator('textarea').fill('Rex is a dog.');await qTab('nibli KR');await run();
  assert.equal(await output.count(),0);checks.push('translated query requires its own exact review and invalidates on edit/revert');
  // A preset is explicitly provided and has its own full-admission path.
  await page.locator('.app-header__examples').selectOption('0');await result('TRUE');await expectText(query.locator('.query-hint'),'Provided example');checks.push('provided preset runs without fabricating personal approval');
  await page.locator('.app-header__examples').selectOption('custom');await run();assert.equal(await output.count(),0);
  await page.reload();await page.locator('.app-shell').waitFor();await run();assert.equal(await output.count(),0);checks.push('approval does not survive tab reload');
  // Mock the provider transport, while retaining the real formalizer, compiler,
  // semantic-status handling, review controls, and async UI application path.
  let delayed = false, notifyRequest;
  const respond = (route,text)=>route.fulfill({status:200,contentType:'application/json',headers:{'access-control-allow-origin':'*'},body:JSON.stringify({choices:[{message:{content:text}}]})});
  await page.route('https://review-test.invalid/**',async route=>{
    if (delayed) { notifyRequest(route); return; }
    const body=route.request().postDataJSON();
    const judge=body.messages.some(message=>message.content?.includes('independent semantic auditor'));
    await respond(route,judge?'Looks fine to me.':'dog(Rex).');
  });
  await topTab('Source');await top.getByTitle('Configure LLM integration').click();
  await page.locator('.llm-provider-btn').filter({hasText:/^Custom$/}).click();
  await page.getByLabel('Base URL',{exact:true}).fill('https://review-test.invalid/v1');
  await page.getByLabel('Model',{exact:true}).fill('review-test');
  await page.getByRole('button',{name:'Save',exact:true}).click();
  await top.locator('textarea').fill('Rex is a dog.');await top.getByRole('button',{name:'Formalize',exact:true}).click();
  await expectText(top.locator('.query-hint'),'unavailable or unparseable');
  await mkdir('/tmp/nibli-ui-browser',{recursive:true});await page.screenshot({path:'/tmp/nibli-ui-browser/approval-panel.png',fullPage:true});
  await run();assert.equal(await output.count(),0);checks.push('malformed semantic check is visibly unavailable and never grants human approval');
  await approve();await qInput().fill('dog(Rex).');await run();await result('TRUE');
  await qTab('Source');await query.locator('textarea').fill('Rex is a dog.');
  delayed=true;let arrived=new Promise(resolve=>{notifyRequest=resolve;});
  await query.getByRole('button',{name:'Formalize',exact:true}).click();let pending=await arrived;
  await qTab('nibli KR');await qInput().fill('cat(Rex).');delayed=false;await respond(pending,'dog(Rex).');
  await expectText(query.locator('.translate-error'),'Discarded a stale query');assert.equal(await qInput().inputValue(),'cat(Rex).');
  checks.push('late query formalization cannot overwrite a newer query revision');
  await topTab('Source');await top.locator('textarea').fill('Rex is a cat.');
  delayed=true;arrived=new Promise(resolve=>{notifyRequest=resolve;});
  await top.getByRole('button',{name:'Formalize',exact:true}).click();pending=await arrived;
  await top.locator('textarea').fill('Rex is a bird.');delayed=false;await respond(pending,'cat(Rex).');
  await expectText(top.locator('.translate-error'),'Discarded a stale formalization');
  await topTab('nibli KR');assert.equal(await kb().inputValue(),'dog(Rex).');
  checks.push('late KB formalization cannot overwrite an edited source or grant approval');
  await mkdir('/tmp/nibli-ui-browser',{recursive:true});await page.screenshot({path:'/tmp/nibli-ui-browser/review-gate.png',fullPage:true});
  assert.deepEqual(errors,[]); console.log(JSON.stringify({checks,pageErrors:errors},null,2));
} catch (error) { await mkdir('/tmp/nibli-ui-browser',{recursive:true}); await page.screenshot({path:'/tmp/nibli-ui-browser/failure.png',fullPage:true}); console.error({checks,errors,body:await page.locator('body').innerText()}); throw error; } finally {await browser.close();await new Promise(resolve=>server.close(resolve));}
