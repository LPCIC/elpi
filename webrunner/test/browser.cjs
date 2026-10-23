// An emulated browser for the tests of the web build: a classic web worker, or
// a page, in a context of node:vm, without process, require or a file system,
// where the builds run as they do in a browser. Its files are the ones of the
// file system, at file: URLs (fetch, importScripts, script elements); a
// scenario takes away what a browser can lack:
//
// - "auto": nothing;
// - "no-wasm-features": WebAssembly.validate fails (an engine without GC,
//   exceptions or tail calls);
// - "wasm-fails": WebAssembly.instantiate and instantiateStreaming fail;
// - "no-wasm-assets": the .wasm files are not there (404);
// - "wrong-mime": the .wasm files are not served as application/wasm;
// - "no-wasm-script": the scripts *.bc.wasm.js are not there.
//
// What the page or the worker loads, and the promises rejected and not
// handled, are written with log (the names of the .wasm files without their
// hash).

const vm = require("node:vm");
const fs = require("node:fs");
const { fileURLToPath } = require("node:url");

const scenarios = ["auto", "no-wasm-features", "wasm-fails", "no-wasm-assets", "wrong-mime", "no-wasm-script"];

function browser({ url, scenario = "auto", page = false, log = () => {}, postMessage = () => {}, close = () => {} }) {
  if (!scenarios.includes(scenario)) throw new Error(`browser: unknown scenario ${scenario}`);
  const name = (u) => new URL(u).pathname.split("/").pop().replace(/^code-[0-9a-f]+\.wasm$/, "*.wasm");

  let wasm = WebAssembly;
  if (scenario !== "auto") {
    wasm = {};
    for (const k of Object.getOwnPropertyNames(WebAssembly)) wasm[k] = WebAssembly[k];
    if (scenario === "no-wasm-features") wasm.validate = () => false;
    if (scenario === "wasm-fails") {
      wasm.instantiate = () => Promise.reject(new Error("WebAssembly.instantiate failed"));
      wasm.instantiateStreaming = () => Promise.reject(new Error("WebAssembly.instantiateStreaming failed"));
    }
  }

  const listeners = new Map();
  const g = vm.createContext({
    console, setTimeout, clearTimeout, setInterval, clearInterval, queueMicrotask,
    TextEncoder, TextDecoder, URL, URLSearchParams, atob, btoa, performance, crypto,
    structuredClone, Response, Headers, Blob, WebAssembly: wasm,
    location: { href: url },
    addEventListener: (type, f) => {
      if (!listeners.has(type)) listeners.set(type, new Set());
      listeners.get(type).add(f);
    },
    removeEventListener: (type, f) => listeners.get(type)?.delete(f),
  });
  vm.runInContext("globalThis.self = globalThis", g);
  const dispatch = (event) => {
    for (const f of [...(listeners.get(event.type) || [])]) f(event);
    return event;
  };

  // a file, or null if it is not there
  const read = (u) => {
    const href = new URL(u, g.location.href);
    if (href.protocol !== "file:") throw new Error(`browser: ${href} is not a file`);
    const file = fileURLToPath(href);
    if (scenario === "no-wasm-script" && file.endsWith(".bc.wasm.js")) return null;
    return fs.existsSync(file) ? { file, data: fs.readFileSync(file) } : null;
  };
  const run = (u) => {
    const f = read(u);
    log(`load ${name(new URL(u, g.location.href))}${f ? "" : ": not found"}`);
    if (!f) throw new Error(`NetworkError: ${u} cannot be loaded`);
    vm.runInContext(f.data.toString("utf8"), g, { filename: f.file });
  };

  g.fetch = async (r, options) => {
    const u = new URL(typeof r === "string" || r instanceof URL ? String(r) : r.url, g.location.href);
    const wasmFile = u.pathname.endsWith(".wasm");
    const f = scenario === "no-wasm-assets" && wasmFile ? null : read(u);
    log(`fetch ${name(u)}${f ? "" : ": 404"}`);
    if (!f) return new Response("not found", { status: 404, statusText: "Not Found" });
    const type = !wasmFile ? "text/plain" : scenario === "wrong-mime" ? "application/octet-stream" : "application/wasm";
    return new Response(f.data, { headers: { "content-type": type } });
  };

  if (page) {
    let current = null;
    g.document = {
      get currentScript() { return current; },
      createElement: () => ({}),
      head: {
        appendChild: (s) => setTimeout(() => {
          current = s;
          try { run(s.src); current = null; s.onload?.(); }
          catch (e) { current = null; s.onerror?.(e); }
        }),
      },
    };
  } else {
    g.importScripts = (...urls) => urls.forEach(run);
    g.postMessage = postMessage;
    g.close = close;
  }

  // the promises rejected and not handled, and the uncaught exceptions
  process.on("unhandledRejection", (reason) => {
    const e = dispatch({ type: "unhandledrejection", reason, defaultPrevented: false,
      preventDefault() { this.defaultPrevented = true; } });
    if (!e.defaultPrevented) log(`unhandled rejection: ${reason && reason.message || reason}`);
  });
  process.on("uncaughtException", (error) => {
    dispatch({ type: "error", error, message: String(error) });
    log(`uncaught exception: ${error && error.message || error}`);
  });

  const parse = vm.runInContext("JSON.parse", g);
  return {
    global: g,
    // runs the script at the URL of the page or of the worker, as a page or
    // a worker does when it starts
    start: () => (page ? g.document.head.appendChild({ src: url }) : run(url)),
    // a message to the worker: the listeners get it, as an object of its realm
    deliver: (data) => dispatch({ type: "message", data: parse(JSON.stringify(data)) }),
    // evaluates code in the page or the worker
    eval: (code) => vm.runInContext(code, g),
  };
}

module.exports = { browser, scenarios };
