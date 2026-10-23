// The tests of the API of Elpi for JavaScript in an emulated browser
// (browser.cjs): elpi-api.js is the script of a page or a classic web worker,
// in a scenario; elpiApi.load() gives the API, which runs a query. What the
// page or the worker loads and the outcome are compared with
// browser.expected. Each case runs in a process of its own.
//
//   node browser-test.cjs path/to/elpi-api.js

const path = require("node:path");
const { pathToFileURL } = require("node:url");
const { spawnSync } = require("node:child_process");
const { browser } = require("./browser.cjs");

// [page or worker, scenario, elpi-api.js loaded by a worker started elsewhere
// with self.elpiApiUrl]
const cases = {
  "worker": ["worker", "auto"],
  "worker, no WebAssembly features": ["worker", "no-wasm-features"],
  "worker, WebAssembly fails": ["worker", "wasm-fails"],
  "worker elsewhere, elpiApiUrl, no WebAssembly features": ["worker", "no-wasm-features", true],
  "page": ["page", "auto"],
  "page, no WebAssembly features": ["page", "no-wasm-features"],
  "page, WebAssembly fails": ["page", "wasm-fails"],
};

const query = `elpiApi.load().then(({ Setup, Parse, Compile, Execute, backend }) => {
  const elpi = Setup.init({});
  const ast = Parse.programFrom(elpi, "pred p o:int.\\np 1. p 2.", { source: "a.elpi" });
  const q = Compile.query(Compile.program(elpi, ast.program).program, Parse.query(elpi, "p X, X > 1.").query);
  return backend + " " + JSON.stringify(Execute.once(Compile.optimize(q.query)));
})`;

const [file, name] = process.argv.slice(2);
if (name === undefined) {
  for (const c of Object.keys(cases)) {
    const r = spawnSync(process.execPath, [__filename, file, c], { encoding: "utf8" });
    process.stdout.write(`== ${c}\n${r.stdout}${r.status === 0 ? "" : `exit ${r.status}\n${r.stderr}`}`);
  }
} else {
  const [mode, scenario, elsewhere] = cases[name];
  const api = pathToFileURL(path.resolve(file)).href;
  const url = elsewhere ? new URL("elsewhere/main.js", api).href : api;
  const b = browser({ url, scenario, page: mode === "page", log: (l) => console.log(l) });
  if (elsewhere) b.eval(`self.elpiApiUrl = ${JSON.stringify(api)}; importScripts(self.elpiApiUrl)`);
  else b.start();
  // a page runs its scripts asynchronously
  const ready = () => b.eval("typeof elpiApi") === "object"
    ? Promise.resolve(b.eval(query)).then((r) => console.log(r), (e) => console.log(`rejected: ${e.message}`))
    : setTimeout(ready, 10);
  ready();
}
