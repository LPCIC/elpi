# Review of the plugin stack (builtin-decls, lift-symbol-lock, dynload)

A review of the commits atop master (424a2c2ab0 .. 333d509297, plus the
uncommitted work on `dynload`). Most items are fixed (below, with their
tests); what is left needs a decision.

## Left: decisions

- 31-bit ints (wasm, js): globals, program constants and the frozen
  constants of a run share about 16M numbers (`Global_symbols.bottom` is
  `-2^(Sys.int_size - 7)`); a long freeze/CHR run can stop with "out of
  constants", where the frozen counter used to be unbounded. Options: accept,
  or give the frozen constants of a run their own range. Not tested ("out of
  constants" cannot be reached on 64-bit).
- Program constants are near -2^56 on 64-bit: an assembled program marshaled
  there cannot be read by a 32-bit runtime; the numbers of late globals
  depend on the order of loading (PLUGIN.md, risk 2). Marshaled units keep
  symbols, not numbers, so only assembled programs are concerned.
- `Global_symbols.highest_used`, `table.last_global`, the variant counters
  and the plugin registry are plain global state: not safe across OCaml 5
  domains (as the rest of Elpi).
- A base checked with stubs gives a program constant to a symbol that a
  plugin declares as a global when it is loaded later: a base cached across
  the load keeps the old number (PLUGIN.md, risk 1). elpi-lsp never loads
  plugins; a host that checks with stubs and then loads must drop its bases.
- "builtin means core or MLCode" is checked by the grammar, the binding of
  builtins files, the type checker and the post check, each for what it
  sees (syntax, OCaml symbols, core symbols, MLCode): one place would need
  the information of all.
- With `builtin_stubs` (elpi-lsp) the checks of user declarations are
  skipped for every file, since a stub cannot be told from a user file (e.g.
  rocq-elpi's coq-builtin.elpi): misuses of `= "core"` that `elpi` rejects
  are not shown by elpi-lsp.
- `MLCalc` operations are found again by file name when a unit is
  assembled: they hold OCaml closures, which units (marshaled) cannot carry.
- The directory of an accumulating file comes from its name cleaned of
  `/_build/CONTEXT`, so `"+/x"` and relative accumulates read the source
  tree: wanted for elpi-lsp, to be kept in mind for dune rules.
- A dev `elpi.toml` declared with the name `json` makes `"+json/x"` read the
  dev tree, while `load` still dynlinks the installed `.cmxs`.
- elpi-lsp reads `elpi.toml` when a document is opened (an edit counts for
  the documents opened after it).
- elpi-json sorts the keys of objects (documented on `json.assoc`).
- Not tested: a global declared while a program runs.

## Fixed

Builtins files:
- `= "N"` is printed only on an overloaded name (several OCaml symbols):
  `Global_symbols.variant_annotation`, used for constructors, opaque
  constants and calc operators. A name with one OCaml symbol is bound by
  name, so the positional pass over the constructors
  (`mark_constructors_of_mldata`) is gone: no more mismatch in namespaces or
  with an `LPCode` symb of the same name. Overloaded constructors in the ppx
  tests now print their variant.
- One function prints a builtins file and returns its implied OCaml symbols
  (`Data.BuiltInPredicate.document_symbols`), instead of two refs set by the
  compiler.
- An OCaml symbol declared twice by its text is an error; a symb with the
  name of an OCaml symbol that the file does not list is an error (it was
  silently an Elpi symbol). This found the constructors of
  `[@elpi.code name code]` in the ppx, printed by hand and not bound: now
  `PPX.Doc.custom_constructor` binds and prints them (with `symb`).
- `context_entry` and a constructor without its OCaml symbol: anomalies.
- A symbol listed twice in `MLConstants`, or listed and implied: bound once.
- The grammar accepts `builtin` with other attributes before `= "core"`, and
  rejects `builtin type` (legacy) as it rejects `builtin symb`.
- `==>` is no longer an alias in the global table (it was not a bijection).

Global symbols:
- The symbol table of a program holds only its own constants; the globals
  are always looked up in `Global_symbols` (one helper), so nothing is
  copied nor goes stale. `same_constants` (was `equal_globals`).
- `global_name_to_constant` falls back to the globals (a bare `Not_found`
  could escape).
- `bottom` is derived from `Discrimination_tree.data_mask`; the schema
  comment says what is below it (nothing).
- The default runtime table starts its frozen constants at `bottom`.
- `Calc.operations` declares no new variant when an operation is built again.
- `vars_of` follows each assigned type variable once.

Plugins and projects:
- A syntax error in a file of `"+pkg/file"`, `"+/file"` or a stub: an error
  of the program, not an exception (the recovery named the file by its raw
  string).
- `API.Utils.string_literal` and `accumulate_text`: the prelude keeps UTF-8
  (OCaml's `%S` wrote `\ddd`, which Elpi does not read), one helper for the
  CLI, the LSP checker and the runner.
- `"+/x"` is a file at the root of the project, the directory of the
  nearest `elpi.toml` (`Setup.packages.root_of_dir`): it no longer goes
  through the name of the project, so two projects with the same name (two
  worktrees) do not mix. The name→root table is filled only by
  `Elpi_dynload.declare_project` (the CLI, elpi-lsp); a renamed project loses
  its old name.
- The search of `elpi.toml` stops at the root of a repository (.git, .hg,
  _darcs, .jj) and never looks in the home directory or above. An LSP
  document with no path (untitled:) has no project.
- One `Plugin.ensure_registered` loads and checks a plugin (core and
  `Elpi_dynload.preload`). A plugin loaded after Setup.init that sets HOAS
  hooks is an error too; the default state descriptor is counted when the
  host gave its own.
- The CLI: the config is found also for `elpi foo` (foo.elpi); with a
  prelude, the main file is found as `Parse.program` finds it (-I) and a
  `.mod` is imported with its `.sig`. Same for the LSP runner.
- TOML subset: escapes (`\n`, `\t`, `\uXXXX` ...), literal strings
  `'...'`, one key per line; `name` is a package name (no `/` nor `\`, not
  empty), and so is the name of `Plugin.register`.
- `"+pkg/"` and `"+"` give their own errors; the extension that accumulate
  appended is removed exactly; on Windows `\` separates the package too.
- The parse cache is per directory, and the digest of a file covers the
  files it accumulates: the same text in two packages resolves its own
  accumulates.
- elpi-lsp: the warnings of the prelude files are not shown in every
  document (their errors are).
- elpi-json: `yojson >= 2.0`.

Tests: tests/sources/plugins.ml (syntax error in a package file, string
literal, duplicate MLConstants, declared twice, unlisted OCaml symbol,
namespaced name, operation built twice, overloaded operator, late quotation,
HOAS hooks, no file, no package, same text in two directories),
tests/plugin/same_name.ml (two projects with the same name, search bounds,
TOML), tests/plugin broken (a dynlink failure), tests/sources/
builtin_core_attrs.elpi, builtin_type.elpi, overload_bare.elpi.
