# Elpi on the web

Elpi in a browser (and in Node), compiled to WebAssembly and to JavaScript:

- the language server `elpi-lsp` (`../lsp/`) in a web worker, used by the VS
  Code extension `gares.elpi-lang` as a fallback, or in vscode.dev, and by the Slidev deck of
  `slidev/`;
- the API of Elpi for JavaScript: parse, compile and run Elpi programs.

```
make webrunner        # webrunner/elpi-webrunner/ (needs lsp, js_of_ocaml, wasm_of_ocaml, node)
make test-webrunner   # the tests, also of the fallbacks (needs node, npx)
```

`webrunner/elpi-webrunner/` is the npm package: `make
pack-webrunner` makes its tarball, versioned by `git describe`, and `make
release` publishes it on npm (`make release-npm`, with the version of the tag
of HEAD). Its metadata and its README are in `npm/`.

## Structure

- `web_lsp_driver.ml`: the server in a web worker, the transport of
  `../lsp/server/`.
- `server-entry.js`: the entry point of the server, `elpi-lsp-web.js`.
- `web_api.ml`: the API of Elpi for JavaScript.
- `api-entry.js`: the entry point of the API, `elpi-api.js`, with its types in
  `elpi-api.d.ts`.
- `assemble.cjs`: makes the entry points from `server-entry.js` and
  `api-entry.js` (it inlines the WebAssembly build of the API).
- `npm/`: the metadata and the README of the npm package.
- `test/`: the tests, see below.
- `slidev/`: Elpi in the slides of a [Slidev](https://sli.dev) deck.

## The server

The worker to start is `elpi-lsp-web.js`: it loads the server compiled to
WebAssembly (`web_lsp_driver.bc.wasm.js` and its assets) when the browser
supports what it needs (GC, exceptions, tail calls) and the files are there,
the one compiled to JavaScript (`web_lsp_driver.bc.js`, which can also be a
worker by itself) otherwise, also when the WebAssembly one fails to start; the files are
served next to each other. The WebAssembly server is about 2-3 times faster.

The messages are JavaScript objects, received by `onmessage` and sent by
`postMessage`. There are no files: `accumulate` fails, and the files of the
standard library are `elpi-builtin:/ID/NAME` documents (see `elpi/builtinFile`
in `../lsp/README.md`). In Node (e.g. the server bundled with the extension for
the desktop) the builds can be run in a `Worker` of `worker_threads` instead,
where `accumulate` reads the files (see `test/server/node-worker.cjs`).

### Stack size

The web server uses the stack much more than the native one.
The JavaScript server answers with the error `internal error: Stack overflow`,
the WebAssembly one dies. A worker of Node can be given a bigger stack:

```js
new Worker(file, { resourceLimits: { stackSizeMb: 64 } })
```

## The API for JavaScript

`web_api.ml` exposes part of the modules `Setup`, `Parse`, `Compile` and
`Execute` of the API of Elpi (`src/API.mli`) to JavaScript. Its entry point
is `elpi-api.js`, the main module of the npm package: its function `load`
gives the API, the same whatever the build it starts:

- the WebAssembly one, which is inlined in `elpi-api.js` (requires Chrome 119,
  Firefox 120, Safari 18.2, Node 22);
- the JavaScript one, `web_api.bc.js`, otherwise, or when the WebAssembly one
  fails to start. It is the only other file, next to `elpi-api.js`.

`load({ backend: "wasm" })` and `load({ backend: "js" })` ask for a build (an
error if it cannot be used). A build is loaded once: the next loads give the
same API. The field `backend` of the API tells which build it is.

`elpi-api.js` is a CommonJS module, also for a bundler, and a script in a page
or in a classic web worker (`importScripts`), where `load` is `elpiApi.load`.
`web_api.bc.js` is found next to it: in Node next to its file, in a page next
to the script, in a worker next to the worker; `self.elpiApiUrl`, the URL of
`elpi-api.js`, overrides the last two (e.g. for a worker started on a `blob:`
URL, or a bundle).

### Example

```js
// In Node, or with a bundler, elpi-api.js is the module of the package. In a
// page (<script src=".../elpi-api.js">) or a classic web worker
// (importScripts(".../elpi-api.js")) it is a script instead: load is then
// elpiApi.load, a global.
const { load } = require("elpi-webrunner");

// Start a build (WebAssembly, or JavaScript as a fallback): the API is the
// same whatever the build, and backend says which one runs.
const { Setup, Parse, Compile, Execute, backend } = await load();

// What the Elpi program prints (e.g. print) goes to this function.
let output = "";
Setup.setStdFormatter((s) => (output += s));

// An instance of Elpi, with the standard builtins.
const elpi = Setup.init({});

// Parse a text: source is its name, used in the locations of the errors.
const ast = Parse.programFrom(elpi, "pred p -> int.\np 1. p 2.", { source: "a.elpi" });
// Compile it: the result is { program, errors, warnings }.
const program = Compile.program(elpi, ast.program);

// Parse a query: the result is { query, warnings }, or { error, warnings }
// if the query has a syntax error.
const goal = Parse.query(elpi, "p X, X > 1.");
// Compile it against the program: again { query, warnings } or
// { error, warnings }, e.g. for a type error.
const query = Compile.query(program.program, goal.query);

// Run it, to its first solution: the values of the variables of the query
// are printed as Elpi prints them.
const outcome = Execute.once(Compile.optimize(query.query));
// outcome is { outcome: "success", assignments: { X: "2" }, constraints: "", state: "" }
```

### Separate compilation

Texts can be compiled separately, as units: a unit is compiled against a base
program, which must have what the unit uses, then the base is extended with
it. `Compile.scopeAst` gives a scoped program for the text and one for each
file it accumulates, to be compiled and added in order.

```js
// The program to extend: it starts with the builtins only.
let base = Compile.emptyBase(elpi);

// The first text: scoped (one scoped program, since it accumulates no file),
// compiled as a unit against the base, then added to the base.
const a = Parse.programFrom(elpi, "pred p -> int.\np 1. p 2.", { source: "a.elpi" });
const [spA] = Compile.scopeAst(elpi, a.program).scopedPrograms;
base = Compile.extend(base, Compile.unit(elpi, base, spA).unit).program;

// The second text uses p, which the base has now.
const b = Parse.programFrom(elpi, "pred main.\nmain :- p X, X > 1, print X.", { source: "b.elpi" });
const [spB] = Compile.scopeAst(elpi, b.program).scopedPrograms;
base = Compile.extend(base, Compile.unit(elpi, base, spB).unit).program;

// A query against the base with both units: it succeeds, and prints 2.
const q = Compile.query(base, Parse.query(elpi, "main.").query);
Execute.once(Compile.optimize(q.query));
```

### Interface

The types are in `elpi-api.d.ts`. In short:

- `load(options?)`: the API, with its `backend`
- `Setup`: `init`, `setStdFormatter`, `setErrFormatter`
- `Parse`: `programFrom`, `query`
- `Compile`: `defaultFlags`, `program`, separate compilation (`scopeAst`,
  `emptyBase`, `unit`, `extend`), `query`, `optimize`
- `Execute`: `once`

The functions have the names of the API in camelCase. The labelled arguments
of the API are positional arguments, and the optional ones are the fields of a
last object, which can be omitted. The abstract types of the API are opaque
values, to be given back to the functions of the API (a value of the wrong
type is not checked at run time).

The parser and the compiler return their errors and their warnings with their
result, e.g. `{ program, errors, warnings }`. An error is `{ component, loc,
message, text }`, where `text` is what Elpi prints. With `flags.maxErrors` 0,
the default, the first error is thrown instead, as an `Error` with the same
fields. A query, parsed (`Parse.query`) or compiled (`Compile.query`), is
`{ query, warnings }`, or `{ error, warnings }` if it has an error.

Accumulated files are read with the file system of Node, through the
`fileResolver` of `Setup.init`; in a browser there are none.

## Tests

`test/browser.cjs` is an emulated browser: a page or a classic web worker in
a context of `node:vm`, without `process`, `require` or a file system, where
the builds run as in a browser, in a scenario that takes away what a browser
can lack (the WebAssembly features, the `.wasm` files, their MIME type, the
WebAssembly scripts), to test the fallbacks.

- `test/server/`: the tests of `../lsp/test/` on the web server, through
  `test/server/bridge.mjs`, a stdio server that forwards the messages to a
  Node worker: both builds run as in Node (`node-js/`, `node-wasm/`), and
  `elpi-lsp-web.js` in the emulated browser in each scenario
  (`browser-SCENARIO/`, without the scripts that accumulate files), where what
  it loads is checked too. The outputs are compared with the ones of the
  native server, but for `good`, `libdef` and `library`, whose expected
  outputs are in `test/server/` (the `elpi-builtin:` URIs).
- `test/api/`: the API through `elpi-api.js`, in Node with each build and
  when WebAssembly cannot be used or fails (`test.cjs`), `load` itself
  (`load.cjs`), and in a page and a worker of the emulated browser
  (`browser-test.cjs`); `types.ts` is typechecked against `elpi-api.d.ts`.

The extension has its own tests in a browser (`npm run test-web` in
elpi-lang).
