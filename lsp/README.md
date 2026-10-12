# elpi-lsp: a language server for Elpi

`elpi-lsp` speaks the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/).

## Quick start

1. Install the dependencies of the server, besides those of Elpi:

       opam install --deps-only ./elpi-lsp.opam

2. Build the server and test it:

       make build-lsp
       make tests-lsp

   The server is built as `_build/install/default/bin/elpi-lsp`.

3. Install the VS Code extension
   [`gares.elpi-lang`](https://github.com/LPCIC/elpi-lang), which starts the
   server; set its `elpi.bin` setting to the directory that contains
   `elpi-lsp` (not needed if it is in the `PATH`).

4. Open a `.elpi` file: syntax errors and type errors are underlined, all of
   them at once; hovering shows types and F12 (Go to Definition) jumps to the
   declaration of a predicate.

## Structure

- `server/`: the server, independent of how messages come and go (the
  library `elpi_lsp_server`):
  - `text.ml`: conversions between byte offsets (Elpi locations) and LSP
    positions (0-based lines, columns in UTF-16 code units).
  - `checker.ml`: runs Elpi's compiler (parsing, type checking ...).
  - `server.ml`: speaks the protocol (see `server.mli`): the documents, the
    requests and notifications, the checks.
  - `library_disk.ml`: the files of the builtins are written on the disk
    on the fly when one jumps to them.
  - `runner.ml`: runs a query on a program, for `elpi/run`.
- `stdio_driver.ml`: the server on stdin/stdout (the executable `elpi-lsp`),
  its main loop driven by [Sel](https://github.com/gares/sel).
- `web_driver.ml`: the server in a web worker, see below.
- `web_api.ml`, `web_api.d.ts`: the API of Elpi for JavaScript, see below.

- `test/`: the tests. `test_lsp_lib.ml` is a client that starts the server and
  drives it with JSON-RPC messages; each `script_*.ml` is the script for one
  `.elpi` file of the directory;
  `test_lsp.ml` runs the scripts, closing the file after each one. The output
  of the script `name` is compared with `test/name.expected`; the rest (the
  capabilities of the server, its shutdown) with `test/test_lsp.expected`. A
  new script needs its output and its comparison to be added to `test/dune`.

## Custom requests

- `elpi/run` runs a query on a program:

  ```ts
  interface RunParams {
    textDocument: { uri: string }  // the document, or where the text is
    query: string                  // e.g. "main", the final "." is optional
    text?: string                  // the program, instead of the document
    maxSteps?: number              // the maximum number of steps of the run
  }
  ```

  The program is the text of the document, or `text` when given: then the
  document needs not be open, and its URI says where the text is, for the
  locations of the errors and to resolve `accumulate`. It can be the URI of a
  directory (it ends with `/`, or it is an existing directory): the text is
  then `(text)` in that directory. The final `.` of the query is optional. The
  result is:

  ```ts
  interface RunResult {
    status: 'success' | 'failure' | 'error'
    output: string        // what the program printed
    errors: string[]      // the errors and warnings of the query and of its run
    diagnostics: string[] // the errors and warnings of the program
    assignments?: { [name: string]: string } // on success: the value of each variable of the query
    constraints?: string[] // on success: the constraints left, as the REPL prints them,
                           // e.g. "{c0} : hyps ?- goal /* suspended on X0 */"
  }
  ```

  `status` is `error` if the query has syntax or type errors, if running
  raises an error, or if the program cannot be compiled at all; a program with
  errors is run anyway, without the declarations and rules that have errors.
  `output` is what the program printed; `diagnostics` are the errors and the
  warnings of the program, with their locations (the ones the server
  publishes as the diagnostics of the document); `errors` are the rest: the
  errors and the warnings of the query and of its run, and last, if the
  program has errors, a warning that it could not be fully compiled.
  The query is run once, by the server itself, for at most
  `maxSteps` steps of the interpreter when given: without it, a query that does
  not terminate blocks the server.

  Running a program executes arbitrary code with the rights of the server: the
  builtins of Elpi can read and write files and start processes.
  In particular a program must not read the standard input or it breaks LSP.

- `elpi/builtinFile` gives the text of a file of the standard library, that
  is built-in the elpi interpreter, for a client that is given it as an
  `elpi-builtin:/NAME` URI (the web server, see below):

  ```ts
  interface BuiltinFileParams {
    uri: string  // e.g. "elpi-builtin:/builtin_stdlib.elpi"
  }
  type BuiltinFileResult = string | null  // the text, null if there is none
  ```

## Web

`web_driver.ml` is the transport for a web worker, used by the
extension `gares.elpi-lang` in vscode.dev.

```
make build-lsp-web      # lsp/elpi-lsp-web/, compiled to JavaScript (needs js_of_ocaml)
make build-lsp-web-wa   # ... and to WebAssembly (needs wasm_of_ocaml)
make tests-lsp-web      # the tests of test/ on the JavaScript build (needs node)
make tests-lsp-web-wa   # ... on the WebAssembly build
```

The worker to start is `lsp/elpi-lsp-web/elpi-lsp-web.js` (from
`web_entry.js`): it loads the server compiled to WebAssembly
(`web_driver.bc.wasm.js` and its assets) when the browser supports what it
needs (GC, exceptions, tail calls) and the files are there, the one compiled
to JavaScript (`web_driver.bc.js`, which can also be a worker by itself)
otherwise; the files are served next to each other. The WebAssembly server is
about 2-3 times faster.

`make release` publishes `lsp/elpi-lsp-web/` on npm as the package
`elpi-lsp-web` (`make release-npm`, with the version of the tag of HEAD); the
metadata and the README of the package are in `npm/`.

The tests run the web build (`test/web/`, and `test/web-wa/` for the
WebAssembly one) in a Node worker through `test/web/bridge.mjs`,
a stdio server that forwards the messages; the outputs are compared with the
ones of the native server, but for `good`, `libdef` and `library`, whose
expected outputs are in `test/web/` (the `elpi-builtin:` URIs). The extension
has its own tests in a browser (`npm run test-web` in elpi-lang).

### Stack size

The web server uses the stack much more than the native one, and the stack of a
worker is small: a deep computation, e.g. `elpi/run` on
`tests/sources/lyp/lyp_engine.elpi`, overflows it. The JavaScript server
answers with the error `internal error: Stack overflow`, the WebAssembly one
dies. A worker of Node can be given a bigger stack:

```js
new Worker(file, { resourceLimits: { stackSizeMb: 64 } })
```

## Performance

- `ELPI_LSP_PROFILE=1` in the environment of the server, or the setting
  `elpi-lsp.debug` set to `messages` or `verbose` in VS Code (the client sends
  it with `$/setTrace`), logs the time of each phase (scoping, each unit, the
  symbols); `verbose` also logs which units come from the cache and how many
  errors each one has.

## Limitations

- A rule that does not type check is dropped from the unit: there is no hover
  in it, and a second error in the same rule is not reported.
- Warnings without a location (e.g. "Undeclared globals") are shown at the
  beginning of the document.
- A dropped declaration (a `pred`, a `type`, a macro) is unknown to the rules
  that use it, which may cause other errors.
- Errors in an accumulated file (also accumulated by another accumulated
  file) are reported on the `accumulate` directive of the document that brings
  it in.
- Only full text synchronization; no completion, no document symbols.

## API for JavaScript

`web_api.ml` exposes part of the modules `Setup`, `Parse`, `Compile` and
`Execute` of the API of Elpi (`src/API.mli`) to JavaScript, compiled to
JavaScript or to WebAssembly. Its types are in `web_api.d.ts`. The builds
are in the npm package `elpi-lsp-web` too (`make build-lsp-web`, then
`lsp/elpi-lsp-web/`), whose main module is the API compiled to JavaScript.

The API is the object `elpi`: `require("web_api.bc.js").elpi` in Node,
`globalThis.elpi` in a browser. The WebAssembly build loads asynchronously:
`elpi` is there once it is loaded (see `getElpi` in `test/web-api/test.cjs`). It finds
its assets next to the main module in Node (`require.main.filename`), next to
the script in a page (`document.currentScript`), relative to the location of a
worker.

### Example

```js
const { Setup, Parse, Compile, Execute } = require("./web_api.bc.js").elpi;

let output = "";
Setup.setStdFormatter((s) => (output += s));
const elpi = Setup.init({});

const ast = Parse.programFrom(elpi, "pred p o:int.\np 1. p 2.", { source: "a.elpi" });
const program = Compile.program(elpi, ast.program);
const goal = Parse.query(elpi, "p X, X > 1."); // { query, warnings } or { error, warnings }
const query = Compile.query(program.program, goal.query);
const outcome = Execute.once(Compile.optimize(query.query));
// { outcome: "success", assignments: { X: "2" }, constraints: "", state: "" }
```

### Separate compilation

Texts can be compiled separately, as units: a unit is compiled against a base
program, which must have what the unit uses, then the base is extended with
it. `Compile.scopeAst` gives a scoped program for the text and one for each
file it accumulates, to be compiled and added in order.

```js
let base = Compile.emptyBase(elpi); // it has the builtins already
const a = Parse.programFrom(elpi, "pred p o:int.\np 1. p 2.", { source: "a.elpi" });
const [spA] = Compile.scopeAst(elpi, a.program).scopedPrograms;
base = Compile.extend(base, Compile.unit(elpi, base, spA).unit).program;

const b = Parse.programFrom(elpi, "pred main.\nmain :- p X, X > 1, print X.", { source: "b.elpi" });
const [spB] = Compile.scopeAst(elpi, b.program).scopedPrograms;
base = Compile.extend(base, Compile.unit(elpi, base, spB).unit).program;

const q = Compile.query(base, Parse.query(elpi, "main.").query);
Execute.once(Compile.optimize(q.query)); // success, prints 2
```

### Interface

The types of the API are in `web_api.d.ts`, which dune copies next to the
builds (`web_api.bc.d.ts`, `web_api.bc.wasm.d.ts`), where TypeScript finds
them. In short:

- `Setup`: `init`, `setStdFormatter`, `setErrFormatter`
- `Parse`: `programFrom`, `goal`
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

Accumulated files are found by the `fileResolver` given to `Setup.init`, and
read with the file system of Node; in a browser there are no files (the
pseudo file system of js_of_ocaml is empty).
