# Ground rules for coding agents

## Build and test
- Build with `make build` (or `dune build`). `make world` also builds
  ppx_elpi and elpi-lsp.
- Run the suite with `make tests SKIP='performance_HO performance_FO'`:
  these two categories are slow benchmarks, skip them unless performance is
  the point.
  `ONLY=rex` narrows the run to tests whose name matches `rex`.
- Also run `make tests-ppx`, `make tests-lsp` and `make tests-webrunner`
  (the web build and its fallbacks; needs node and npx); all three accept
  `PROMOTE=true`, with the exception explained below.
- New end-to-end tests: put the program in `tests/sources/NAME.elpi` (with a
  `main`), and register it with `declare` in the matching
  `tests/suite/*.ml` file (`elpi_specific.ml` for most features), with an
  expectation such as `SuccessOutput (Str.regexp_string "...")`.
- `src/builtin.elpi` is generated from `src/builtin.ml` by the build
  (`elpi -document-builtins`, promoted by dune). Never edit it by hand;
  rebuild and check its diff.
- Some tests store full traces (`tests/sources/trace_*.json`,
  `trace_*.elab.json`) that record line/character positions in
  `builtin.elpi` and internal constant numbers (`frozen--NNN`). Any change to
  the builtins shifts them. Check that the diff is only positions, then
  regenerate with `make tests ONLY='trace-browser' PROMOTE=true`.
- The LSP test expectations can contain offsets too (positions in
  `builtin.elpi`), so they shift for the same reason: check the diff is only
  positions, then regenerate with `make tests-lsp PROMOTE=true`.
- The webrunner tests replay the LSP tests on the web build. They compare
  with `webrunner/test/server/NAME.expected` when that file exists, and with
  `lsp/test/NAME.expected` otherwise. The comparison is done by
  `webrunner/test/server/compare.cjs`, which `PROMOTE=true` does not reach:
  update a web-specific `NAME.expected` by hand, copying
  `_build/default/webrunner/test/server/node-js/NAME.output` over it after
  checking that the diff is only positions.

## OCaml code
- Do not use polymorphic equality (`=`, `<>`, `compare`, `List.mem`) when a
  dedicated function exists: `String.equal`, `Int.compare`, `Loc.equal`,
  `Option.is_none` / `Option.is_some`, `List.exists (String.equal x)`.
  Plain `=` stays acceptable on ints, chars and variants without an `equal`.
- Keep the code compatible with OCaml 4.14, the lowest supported version:
  for example no `List.is_empty`.
- Formatting follows `.ocamlformat` (margin 120).
- Builtins are declared through the FFI in `src/builtin.ml` (`MLCode`,
  `MLData`, `AlgebraicData`, `OpaqueData`); follow the existing entries and
  give each one a doc string, since it ends up in `builtin.elpi`.

## Reference manual (`docs/base`, Sphinx)
- Build with `make doc-build`; it must stay free of new warnings and of
  "Injection failure" boxes.
- Every code example is an external file under `docs/base/code/`, included
  with `.. elpi:: code/NAME.elpi` (path relative to the `.rst` file) followed
  by `   :assert: REGEXP` pinning its standard output.
- Verify every fact against the implementation (run it), not against other
  documentation.
- Terminology: a `pred` / `func` line is a *signature*; a `head :- body` unit
  is a *rule*, never a *clause*.
- A `:doc:` / `:ref:` link is never the subject or predicate noun of a
  sentence: write "is described in :doc:`x`", not ":doc:`x` describes".
- No `**bold**` in prose; `*italic*` for a term's first use, ``literal`` for
  code. Legacy syntax only in `compatibility.rst`.
- Do not reintroduce text a maintainer deleted.

## Workflow
- User-visible changes get an entry in `CHANGES.md` under `# Unreleased`
  (create the section at the top if missing).
- Never commit unless asked to. Commit messages have no `Co-Authored-By`
  trailer.
