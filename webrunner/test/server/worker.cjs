// The worker of bridge.mjs: an emulated browser (../browser.cjs) runs the
// entry point of the server, elpi-lsp-web.js, as a web worker, in a scenario;
// it loads the server it picks. Its messages go to bridge.mjs, and the ones of
// bridge.mjs come to it.
const { parentPort, workerData } = require("node:worker_threads");
const fs = require("node:fs");
const { pathToFileURL } = require("node:url");
const { browser } = require("./browser.cjs");

const { entry, scenario, log } = workerData;
fs.writeFileSync(log, "");
const worker = browser({
  url: pathToFileURL(entry).href,
  scenario,
  log: (line) => fs.appendFileSync(log, line + "\n"),
  postMessage: (m) => parentPort.postMessage(m),
  close: () => process.exit(0),
});
parentPort.on("message", (data) => worker.deliver(data));
worker.start();
