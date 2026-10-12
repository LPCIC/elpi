# elpi-lsp: a language server for Elpi

`elpi-lsp` speaks the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
on stdin/stdout. 

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
  `elpi-builtin:/NAME` URI:

  ```ts
  interface BuiltinFileParams {
    uri: string  // e.g. "elpi-builtin:/builtin_stdlib.elpi"
  }
  type BuiltinFileResult = string | null  // the text, null if there is none
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
