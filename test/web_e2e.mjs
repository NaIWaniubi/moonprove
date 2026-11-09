// End-to-end test for the browser build: load the page, type a spec, read the
// verdicts out of the DOM. If the bundle and the page ever disagree, this fails.
import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { readFileSync, mkdtempSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const root = path.dirname(path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, '$1')));
const port = 9311 + Math.floor(Math.random() * 200);
const profile = mkdtempSync(path.join(tmpdir(), 'moonprove-e2e-'));

const server = createServer((req, res) => {
  const name = req.url === '/' ? 'index.html' : req.url.replace(/^\//, '');
  try {
    const body = readFileSync(path.join(root, 'web', name));
    const type = name.endsWith('.js') ? 'text/javascript' : 'text/html; charset=utf-8';
    res.writeHead(200, { 'content-type': type });
    res.end(body);
  } catch {
    res.writeHead(404);
    res.end('not found');
  }
});
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const base = `http://127.0.0.1:${server.address().port}`;

const chrome = 'C:/Program Files/Google/Chrome/Application/chrome.exe';
if (!existsSync(chrome)) {
  console.log('web e2e skipped: no Chrome at ' + chrome);
  process.exit(0);
}
const proc = spawn(
  chrome,
  [
    '--headless=new', '--disable-gpu', '--no-sandbox', '--no-first-run',
    `--user-data-dir=${profile}`, `--remote-debugging-port=${port}`, 'about:blank',
  ],
  { windowsHide: true, stdio: 'ignore' },
);
proc.on('error', (e) => { console.error('chrome failed to start: ' + e.message); process.exit(2); });

async function json(url, tries = 80) {
  for (let i = 0; i < tries; i++) {
    try {
      const r = await fetch(url);
      if (r.ok) return await r.json();
    } catch {}
    await new Promise((r) => setTimeout(r, 250));
  }
  throw new Error('no CDP at ' + url);
}

let ws;
try {
  // Wait for the page target Chrome opens on startup.
  let target = null;
  for (let i = 0; i < 80 && target === null; i++) {
    try {
      const list = await (await fetch(`http://127.0.0.1:${port}/json/list`)).json();
      target = list.find((t) => t.type === 'page') ?? null;
    } catch {}
    if (target === null) await new Promise((r) => setTimeout(r, 250));
  }
  if (target === null) throw new Error('no page target');
  ws = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((res, rej) => { ws.onopen = res; ws.onerror = rej; });
  let nextId = 1;
  const waiting = new Map();
  ws.onmessage = (ev) => {
    const msg = JSON.parse(ev.data);
    if (msg.id && waiting.has(msg.id)) {
      waiting.get(msg.id)(msg);
      waiting.delete(msg.id);
    }
  };
  const send = (method, params) =>
    new Promise((res) => {
      const id = nextId++;
      waiting.set(id, res);
      ws.send(JSON.stringify({ id, method, params }));
    });
  const evaluate = async (expr) => {
    const r = await send('Runtime.evaluate', { expression: expr, awaitPromise: true, returnByValue: true });
    if (r.result?.exceptionDetails) {
      throw new Error('page exception: ' + (r.result.exceptionDetails.text ?? '') + ' ' +
        JSON.stringify(r.result.exceptionDetails.exception?.description ?? '').slice(0, 300));
    }
    return r.result?.result?.value;
  };

  await send('Page.enable');
  await send('Runtime.enable');
  await send('Page.navigate', { url: base + '/' });
  // Poll until the page's own script has run (it sets the gutter).
  let ready = false;
  for (let i = 0; i < 60 && !ready; i++) {
    await new Promise((r) => setTimeout(r, 250));
    const state = await send('Runtime.evaluate', {
      expression: `document.getElementById('gutter')?.childElementCount > 0`,
      returnByValue: true,
    });
    ready = state.result?.result?.value === true;
  }
  if (!ready) {
    const why = await send('Runtime.evaluate', {
      expression: `document.body.innerText.slice(0, 400)`,
      returnByValue: true,
    });
    throw new Error('page never rendered; body: ' + JSON.stringify(why.result?.result?.value));
  }

  const pageErrors = await evaluate(`JSON.stringify({
    err: window.__lastError ?? null,
    hasBundle: typeof window.moonProveWriteOutput,
    results: document.querySelectorAll('.verdict').length,
    count: document.getElementById('count').textContent,
    body: document.getElementById('results').textContent.slice(0, 200),
  })`);
  console.log('page state: ' + pageErrors);
  const counts = await evaluate(`JSON.stringify({
    proven: document.getElementById('c-proven').textContent,
    violated: document.getElementById('c-violated').textContent,
    unknown: document.getElementById('c-unknown').textContent,
    count: document.getElementById('count').textContent,
    firstChip: document.querySelector('.verdict .chip')?.textContent ?? null,
  })`);
  const parsed = JSON.parse(counts);
  if (parsed.count !== '2 条') throw new Error('expected 2 obligations, got ' + parsed.count);
  if (parsed.proven !== '2') throw new Error('expected both proven, got ' + parsed.proven);

  // A violated spec must surface its counterexample text.
  await evaluate(`(() => {
    const t = document.getElementById('src');
    t.value = ['fn wrong(x : Int) -> Int {', '  assert x > 100', '  return x', '}'].join(String.fromCharCode(10));
    t.dispatchEvent(new Event('input'));
  })()`);
  await new Promise((r) => setTimeout(r, 1500));
  const ce = await evaluate(`document.querySelector('.verdict.violated .ce')?.textContent ?? null`);
  if (!ce || !ce.includes('=')) throw new Error('no counterexample rendered: ' + ce);
  console.log('web e2e ok: ' + parsed.count + ', both proven, counterexample ' + ce);
} catch (error) {
  console.error('web e2e FAILED: ' + error.message);
  process.exitCode = 1;
} finally {
  try { ws?.close(); } catch {}
  proc.kill();
  server.close();
  await new Promise((r) => setTimeout(r, 600));
  try { rmSync(profile, { recursive: true, force: true }); } catch {}
}
