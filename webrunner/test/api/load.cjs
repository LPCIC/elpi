// The tests of load, the entry point of the API (elpi-api.js), in Node: what it
// gives or why it fails, compared with load.expected. Each case runs in a
// process of its own (a build is loaded once per process).
//
//   node load.cjs path/to/elpi-api.js

const path = require("node:path");
const { spawnSync } = require("node:child_process");

const cases = {
  // a backend that is not one
  "unknown backend": async (load) => load({ backend: "native" }),
  // WebAssembly asked for, but the engine lacks what it needs, or it fails
  "wasm without the features": async (load) => {
    WebAssembly.validate = () => false;
    return load({ backend: "wasm" });
  },
  "wasm that fails": async (load) => {
    WebAssembly.instantiate = () => Promise.reject(new Error("WebAssembly.instantiate failed"));
    return load({ backend: "wasm" });
  },
  // a build is loaded once: the same API again, or an error if it is not the
  // build asked for
  "auto twice": async (load) => {
    const a = await load();
    return { same: a === (await load()), backend: a.backend };
  },
  "js, then auto": async (load) => {
    const a = await load({ backend: "js" });
    return { same: a === (await load()), backend: a.backend };
  },
  "js, then wasm": async (load) => {
    await load({ backend: "js" });
    return load({ backend: "wasm" });
  },
  // a failed load can be tried again
  "wasm that fails, then js": async (load) => {
    WebAssembly.validate = () => false;
    await load({ backend: "wasm" }).catch(() => {});
    return (await load({ backend: "js" })).backend;
  },
  // the API is frozen
  "frozen": async (load) => Object.isFrozen(await load()),
};

const [file, name] = process.argv.slice(2);
if (name === undefined) {
  for (const c of Object.keys(cases)) {
    const r = spawnSync(process.execPath, [__filename, file, c], { encoding: "utf8" });
    process.stdout.write(`${c}: ${r.stdout.trim()}${r.status === 0 ? "" : ` (exit ${r.status}) ${r.stderr}`}\n`);
  }
} else {
  const { load } = require(path.resolve(file));
  cases[name](load).then(
    (v) => console.log(JSON.stringify(v && v.Setup ? `the ${v.backend} build` : v)),
    (e) => console.log(`${e.constructor.name}: ${e.message}`));
}
