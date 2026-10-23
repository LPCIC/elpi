// The worker of bridge.mjs in Node mode: postMessage, onmessage and close as
// in a web worker, then the server (its path is the data of the worker), which
// runs as in Node (e.g. the server bundled with the extension elpi-lang for
// the desktop), where accumulate reads the files. It is a file,
// not evaluated code: the WebAssembly server finds its assets next to the
// main module. The WebAssembly server starts asynchronously: the messages
// that arrive before it sets onmessage are queued, as web_entry.js does.
const { parentPort, workerData } = require("node:worker_threads");
globalThis.postMessage = (m) => parentPort.postMessage(m);
globalThis.close = () => process.exit(0);
let handler = null;
const queue = [];
Object.defineProperty(globalThis, "onmessage", {
  get: () => handler,
  set: (f) => {
    handler = f;
    while (handler && queue.length) handler({ data: queue.shift() });
  },
});
parentPort.on("message", (data) => (handler ? handler({ data }) : queue.push(data)));
// the WebAssembly server finds its assets next to the main module: the server
process.mainModule = { filename: workerData };
require(workerData);
