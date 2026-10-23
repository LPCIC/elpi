// A stdio language server made of the web build of elpi-lsp, for the tests:
// the messages read on stdin (with Content-Length headers) are posted to the
// server, run in a worker thread as in a web worker, and its messages are
// written on stdout. Either
//
//   node bridge.mjs node path/to/web_lsp_driver.bc.js
//
// a server (or web_lsp_driver.bc.wasm.js) run as in Node (node-worker.cjs), or
//
//   node bridge.mjs browser path/to/elpi-lsp-web.js SCENARIO LOG
//
// the entry point elpi-lsp-web.js, run in an emulated browser in a scenario
// of ../browser.cjs, that picks the server (worker.cjs); what it loads is
// written in LOG.

import { Worker } from "node:worker_threads";
import { resolve } from "node:path";

const [mode, file, scenario, log] = process.argv.slice(2);
const [script, workerData] = mode === "node"
  ? ["./node-worker.cjs", resolve(file)]
  : ["./worker.cjs", { entry: resolve(file), scenario, log: resolve(log) }];

// with the default stack size, small as in a browser (resourceLimits.
// stackSizeMb would make it bigger, see "Stack size" in ../../README.md)
const worker = new Worker(new URL(script, import.meta.url), { workerData, stdout: false, stderr: false });

worker.on("message", (m) => {
  const body = Buffer.from(JSON.stringify(m), "utf8");
  process.stdout.write(`Content-Length: ${body.length}\r\n\r\n`);
  process.stdout.write(body);
});
worker.on("exit", (code) => process.exit(code));
worker.on("error", (e) => { console.error(e); process.exit(1); });

// the messages of the client
let buffer = Buffer.alloc(0);
process.stdin.on("data", (chunk) => {
  buffer = Buffer.concat([buffer, chunk]);
  for (;;) {
    const end = buffer.indexOf("\r\n\r\n");
    if (end < 0) return;
    const m = /Content-Length: *(\d+)/i.exec(buffer.subarray(0, end).toString("ascii"));
    if (!m) { console.error("bridge: no Content-Length"); process.exit(1); }
    const length = Number(m[1]);
    if (buffer.length < end + 4 + length) return;
    const body = buffer.subarray(end + 4, end + 4 + length).toString("utf8");
    buffer = buffer.subarray(end + 4 + length);
    worker.postMessage(JSON.parse(body));
  }
});
process.stdin.on("end", () => worker.terminate());
