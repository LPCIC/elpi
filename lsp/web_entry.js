// The entry point of elpi-lsp for the web, run as a (classic) web worker:
// it loads the server compiled to WebAssembly (web_driver.bc.wasm.js and its
// assets) when the browser supports what it needs and the files are there,
// the server compiled to JavaScript (web_driver.bc.js) otherwise. They are
// next to this file (make build-lsp-web, make build-lsp-web-wa), which is
// self.location, or self.elpiLspWebUrl when the worker is not started on this
// file: e.g. VS Code for the web starts the workers of the extensions as blob:
// URLs that import the script, a client there starts this one as
//   self.elpiLspWebUrl = "https://.../elpi-lsp-web.js"; importScripts(self.elpiLspWebUrl);
(() => {
  const base = self.elpiLspWebUrl || self.location.href;
  const load = (file) => importScripts(new URL(file, base).href);
  // the WebAssembly server fetches its assets with relative URLs
  const fetch = self.fetch.bind(self);
  self.fetch = (r, o) => fetch(typeof r === "string" ? new URL(r, base).href : r, o);

  // The messages of the client are given to the onmessage of the server. The
  // WebAssembly server starts asynchronously: the messages that arrive before
  // it sets onmessage are queued, and given to it when it does.
  let handler = null;
  const queue = [];
  self.addEventListener("message", (e) => (handler ? handler(e) : queue.push(e)));
  Object.defineProperty(self, "onmessage", {
    configurable: true,
    get: () => handler,
    set: (f) => {
      handler = f;
      while (handler && queue.length) handler(queue.shift());
    },
  });

  // a module that uses what the WebAssembly server needs: GC, the (legacy)
  // exception handling, tail calls
  const features = new Uint8Array([
    0, 97, 115, 109, 1, 0, 0, 0, 1, 12, 3, 96, 0, 1, 127, 95, 1, 127, 0, 96, 0,
    0, 3, 3, 2, 0, 0, 13, 3, 1, 0, 2, 7, 5, 1, 1, 102, 0, 0, 10, 26, 2, 4, 0,
    18, 1, 11, 19, 0, 6, 64, 8, 0, 7, 0, 1, 11, 65, 1, 251, 0, 1, 251, 2, 1, 0,
    11,
  ]);
  const javascript = () => load("web_driver.bc.js");
  if (typeof WebAssembly === "object" && WebAssembly.validate(features)) {
    // the WebAssembly server fails to start (e.g. its assets are missing)
    // before setting onmessage: the JavaScript one is loaded instead
    self.addEventListener("unhandledrejection", (e) => {
      if (handler === null) { e.preventDefault(); javascript(); }
    });
    try {
      load("web_driver.bc.wasm.js");
      return;
    } catch (_) {
      // not built
    }
  }
  javascript();
})();
