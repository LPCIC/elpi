// A stdio language server made of the web build of elpi-lsp, for the tests:
// the messages read on stdin (with Content-Length headers) are posted to the
// server, run in a worker thread as in a web worker, and its messages are
// written on stdout.
//
//   node bridge.mjs path/to/elpi-lsp-web.js

import { Worker } from "node:worker_threads";
import { resolve } from "node:path";

const server = resolve(process.argv[2]);

// in the worker: postMessage, onmessage and close as in a web worker, then
// the server
const worker = new Worker(`
  const { parentPort } = require("node:worker_threads");
  globalThis.postMessage = (m) => parentPort.postMessage(m);
  globalThis.close = () => process.exit(0);
  parentPort.on("message", (data) => globalThis.onmessage({ data }));
  require(${JSON.stringify(server)});
`, { eval: true, stdout: false, stderr: false });

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
