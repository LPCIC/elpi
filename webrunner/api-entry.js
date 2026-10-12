// The API of Elpi for JavaScript, elpi-api.js (assemble.cjs makes it from this
// file): load() starts the API compiled to WebAssembly, which is inlined here,
// when the JavaScript engine supports what it needs (GC, exceptions, tail
// calls), and the API compiled to JavaScript, web_api.bc.js next to this file,
// otherwise or when the WebAssembly one fails to start. Both are web_api.ml and
// give the same API (see elpi-api.d.ts), with the field backend telling which
// one it is. In Node and with a bundler it is a CommonJS module; in a page (a
// script) and in a classic web worker (importScripts) load is elpiApi.load.
//
// web_api.bc.js is found next to __dirname in Node, next to this script in a
// page, next to the worker otherwise; self.elpiApiUrl, the URL of this file,
// overrides the last two (e.g. for a worker started on a blob: URL).
(() => {
  "use strict";
  const scope = globalThis;
  const node = typeof module === "object" && typeof require === "function" &&
    typeof process === "object" && !!process.versions?.node;
  const script = !node && typeof document === "object" ? document.currentScript : null;
  const base = () => scope.elpiApiUrl || script?.src || scope.location?.href;

  const features = /*@WASM_FEATURES@*/;
  const wasmSupported = () => typeof WebAssembly === "object" && WebAssembly.validate(features);

  // the .wasm files of the WebAssembly build, and the one a path or a URL
  // names, if any
  const wasmFiles = /*@WASM_FILES@*/;
  function wasmFile(p) {
    const name = String(p).replace(/[?#].*$/, "").split(/[\\/]/).pop();
    if (!Object.prototype.hasOwnProperty.call(wasmFiles, name)) return null;
    return Uint8Array.from(atob(wasmFiles[name]), (c) => c.charCodeAt(0));
  }

  // The WebAssembly build, the script made by wasm_of_ocaml (it starts
  // asynchronously). It reads its .wasm files with require("node:fs/promises")
  // in Node, with fetch otherwise: these are the ones it is given, which read
  // the inlined files.
  function wasmBuild(require, fetch) {
    /*@WASM_LOADER@*/
  }

  function startWasm() {
    if (node) {
      const fsp = require("node:fs/promises");
      const readFile = (p, ...args) => {
        const bytes = wasmFile(p);
        return bytes ? Promise.resolve(bytes) : fsp.readFile(p, ...args);
      };
      const wasmRequire = (m) => (m === "node:fs/promises" ? { ...fsp, readFile } : require(m));
      wasmRequire.main = { filename: __filename };
      wasmBuild.call(scope, wasmRequire, scope.fetch);
    } else {
      const fetch = (r, options) => {
        const bytes = typeof r === "string" || r instanceof URL ? wasmFile(r) : null;
        if (!bytes) return scope.fetch(r, options);
        return Promise.resolve(new Response(bytes, { headers: { "content-type": "application/wasm" } }));
      };
      wasmBuild.call(scope, undefined, fetch);
    }
    return false;
  }

  // The JavaScript build, which starts synchronously, but in a page; returns
  // whether it is started
  const jsFile = "web_api.bc.js";
  function startJs(fail) {
    if (node) {
      require(require("node:path").join(__dirname, jsFile));
      return true;
    }
    const url = new URL(jsFile, base()).href;
    if (typeof importScripts === "function") {
      importScripts(url);
      return true;
    }
    if (typeof document === "object") {
      const s = document.createElement("script");
      s.src = url;
      s.onerror = () => fail(new Error(`elpi-api: cannot load ${url}`));
      s.onload = () => fail(new Error(`elpi-api: ${url} did not start`));
      document.head.appendChild(s);
      return false;
    }
    throw new Error("elpi-api: cannot load the JavaScript build here");
  }

  // Starts a build, which gives the API to globalThis.__elpiApiReady. It
  // fails if start throws or calls fail, if a synchronous start does not give
  // the API, or if a promise is rejected and not handled meanwhile (the start
  // of the WebAssembly build is asynchronous, its errors are not caught).
  function run(start) {
    return new Promise((resolve, reject) => {
      let settled = false;
      const onRejection = node
        ? (reason) => settle(reject, reason)
        : (e) => { e.preventDefault(); settle(reject, e.reason); };
      function settle(f, v) {
        if (settled) return;
        settled = true;
        delete scope.__elpiApiReady;
        if (node) process.off("unhandledRejection", onRejection);
        else scope.removeEventListener?.("unhandledrejection", onRejection);
        f(v);
      }
      scope.__elpiApiReady = (api) => settle(resolve, api);
      if (node) process.on("unhandledRejection", onRejection);
      else scope.addEventListener?.("unhandledrejection", onRejection);
      try {
        if (start((e) => settle(reject, e))) settle(reject, new Error("elpi-api: the build did not start"));
      } catch (e) {
        settle(reject, e);
      }
    });
  }

  async function start(backend) {
    if (backend !== "js") {
      if (wasmSupported()) {
        try {
          return { api: await run(startWasm), backend: "wasm" };
        } catch (e) {
          if (backend === "wasm") throw e;
        }
      } else if (backend === "wasm") {
        throw new Error("elpi-api: this JavaScript engine lacks what the WebAssembly build needs (GC, exceptions, tail calls)");
      }
    }
    return { api: await run(startJs), backend: "js" };
  }

  // A build is loaded once: the next loads give the same API, if it is of the
  // backend they ask for. A failed load can be tried again.
  const backends = ["auto", "wasm", "js"];
  let loading = null;
  function load(options = {}) {
    const backend = options.backend ?? "auto";
    if (!backends.includes(backend))
      return Promise.reject(new TypeError(`elpi-api: the backend is one of ${backends.join(", ")}`));
    if (!loading) {
      const p = start(backend).then(({ api, backend }) => Object.freeze({
        Setup: api.Setup, Parse: api.Parse, Compile: api.Compile, Execute: api.Execute, backend,
      }));
      loading = p;
      p.catch(() => { if (loading === p) loading = null; });
    }
    return loading.then((api) => backend === "auto" || api.backend === backend ? api
      : Promise.reject(new Error(`elpi-api: the ${api.backend} build is loaded already`)));
  }

  if (typeof module === "object" && module && module.exports) module.exports = { load };
  else scope.elpiApi = { load };
})();
