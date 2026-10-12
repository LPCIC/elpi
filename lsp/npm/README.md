# elpi-lsp-web

The language server of [Elpi](https://github.com/LPCIC/elpi) (diagnostics,
hover, go to definition, highlights, semantic tokens, `elpi/run`) for the web,
run in a web worker. It is used by the VS Code extension `gares.elpi-lang` in
vscode.dev, and by the Slidev integration of the Elpi repository
(`etc/slidev`). The package also has the API of Elpi for JavaScript (parse,
compile and run Elpi programs), see below.

## Content

- `elpi-lsp-web.js`: the entry point, the script of the worker. It loads the
  server compiled to WebAssembly when the browser supports what it needs (GC,
  exceptions, tail calls: Chrome 119, Firefox 120, Safari 18.2) and the
  `.wasm` files are served as `application/wasm`, the server compiled to
  JavaScript otherwise.
- `web_driver.bc.wasm.js` and `web_driver.bc.wasm.assets/`: the server
  compiled to WebAssembly.
- `web_driver.bc.js`: the server compiled to JavaScript.
- `web_api.bc.js` (the main module of the package) and `web_api.bc.wasm.js`
  with `web_api.bc.wasm.assets/`: the API for JavaScript, compiled to
  JavaScript and to WebAssembly, with their types (`web_api.bc.d.ts`,
  `web_api.bc.wasm.d.ts`).

## Use

The files are not a module to bundle: serve them as static files, next to each
other, e.g. by copying the package to the public directory of the site, and
start the worker on the entry point:

```js
const worker = new Worker("/elpi-lsp-web/elpi-lsp-web.js");
```

The worker speaks the Language Server Protocol with JSON messages: post a
message to send it to the server, its messages are the ones of the worker.
There are no files: `accumulate` fails, and the files of the standard library
are `elpi-builtin:/NAME` documents, whose text the request `elpi/builtinFile`
returns.

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
part; the types are in `web_api.bc.d.ts`, and the documentation in the README
of the language server of Elpi (`lsp/README.md`, "API for JavaScript").

```js
const { Setup, Parse, Compile, Execute } = require("elpi-lsp-web").elpi;

const elpi = Setup.init({});
const ast = Parse.programFrom(elpi, "pred p o:int.\np 1. p 2.", { source: "a.elpi" });
const program = Compile.program(elpi, ast.program);
const query = Compile.query(program.program, Parse.query(elpi, "p X, X > 1.").query);
Execute.once(Compile.optimize(query.query));
// { outcome: "success", assignments: { X: "2" }, constraints: "", state: "" }
```

The main module is the API compiled to JavaScript. The one compiled to
WebAssembly (`web_api.bc.wasm.js`) loads asynchronously (`elpi` is there once
it is loaded) and, in Node, finds its assets next to the main module of the
program (`require.main.filename`): set `process.mainModule = { filename }` to
its file before requiring it.

## License

LGPL-2.1-or-later, as Elpi.
