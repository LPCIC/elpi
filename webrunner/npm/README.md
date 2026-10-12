# elpi-webrunner

The language server of [Elpi](https://github.com/LPCIC/elpi) (diagnostics,
hover, go to definition, highlights, semantic tokens, `elpi/run`) for the web,
run in a web worker. It is used by the VS Code extension `gares.elpi-lang` in
vscode.dev, and by the Slidev integration of the Elpi repository
(`webrunner/slidev`). The package also has the API of Elpi for JavaScript
(parse, compile and run Elpi programs), see below.

## Content

- `elpi-lsp-web.js`: the entry point, the script of the worker. It loads the
  server compiled to WebAssembly when the browser supports what it needs (GC,
  exceptions, tail calls: Chrome 119, Firefox 120, Safari 18.2) and the
  `.wasm` files are served as `application/wasm`, the server compiled to
  JavaScript otherwise.
- `web_lsp_driver.bc.wasm.js` and `web_lsp_driver.bc.wasm.assets/`: the server
  compiled to WebAssembly.
- `web_lsp_driver.bc.js`: the server compiled to JavaScript.
- `elpi-api.js` (the main module of the package): the API for JavaScript,
  compiled to WebAssembly (inlined), with its types (`elpi-api.d.ts`).
- `web_api.bc.js`: the API compiled to JavaScript, which `elpi-api.js` loads
  when the WebAssembly one cannot be used.

## The server

The server is not a module to bundle: serve its files as static files, next
to each other, e.g. by copying the package to the public directory of the
site, and start the worker on the entry point:

```js
const worker = new Worker("/elpi-webrunner/elpi-lsp-web.js");
```

The worker speaks the Language Server Protocol with JSON messages: post a
message to send it to the server, its messages are the ones of the worker.
There are no files: `accumulate` fails, and the files of the standard library
are `elpi-builtin:/ID/NAME` documents (ID is the instance of Elpi of the
document they come from), whose text the request `elpi/builtinFile` returns
while that document is open.

When the worker is not started on the URL of `elpi-lsp-web.js` (e.g. VS Code
for the web starts the workers of the extensions as `blob:` URLs that import
the script), set `self.elpiLspWebUrl` to it: the entry point loads the servers
next to it.

```js
const boot = `self.elpiLspWebUrl = ${JSON.stringify(url)}; importScripts(self.elpiLspWebUrl);`;
const worker = new Worker(URL.createObjectURL(new Blob([boot], { type: "application/javascript" })));
```

## Stack size

The server uses the stack much more than the native one, and the stack of a
web worker is small and cannot be changed: a deep computation can overflow it
(the JavaScript server answers with an error, the WebAssembly one dies). In
Node, a `Worker` of `worker_threads` can be given a bigger stack with
`resourceLimits: { stackSizeMb: 64 }`; the WebAssembly server then needs
`process.mainModule` to be set to its file, to find its assets.

## API for JavaScript

The modules `Setup`, `Parse`, `Compile` and `Execute` of the API of Elpi, in
part; the types are in `elpi-api.d.ts`, and the documentation in the README
of `webrunner/` in the Elpi repository.

```js
const { load } = require("elpi-webrunner"); // or: import { load } from "elpi-webrunner"
const { Setup, Parse, Compile, Execute, backend } = await load();

const elpi = Setup.init({});
const ast = Parse.programFrom(elpi, "pred p o:int.\np 1. p 2.", { source: "a.elpi" });
const program = Compile.program(elpi, ast.program);
const query = Compile.query(program.program, Parse.query(elpi, "p X, X > 1.").query);
Execute.once(Compile.optimize(query.query));
// { outcome: "success", assignments: { X: "2" }, constraints: "", state: "" }
```

`load` starts the API compiled to WebAssembly, which is inlined in
`elpi-api.js`, when the JavaScript engine supports what it needs (GC,
exceptions, tail calls: Chrome 119, Firefox 120, Safari 18.2, Node 22), and
the one compiled to JavaScript, `web_api.bc.js`, otherwise or when the
WebAssembly one fails to start; `backend` is `"wasm"` or `"js"`, and
`load({ backend })` asks for one. Both give the same API. A build is loaded
once: the next loads give the same API.

In a page or a classic web worker, `elpi-api.js` is a script (`<script>`,
`importScripts`) and `load` is `elpiApi.load`. Serve `web_api.bc.js` next to
`elpi-api.js`: it is found next to the script in a page, next to the worker
in a worker, or next to `self.elpiApiUrl`, the URL of `elpi-api.js`, if set
(e.g. in a worker started on a `blob:` URL, or with a bundler).

## License

LGPL-2.1-or-later, as Elpi.
