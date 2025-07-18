# v3.0.1 (July 2025)

- Language:
  - Improve error message for non deterministic atom
  - Fix overlap check for `uvar F L as X`
  - Fix allow `symbol` as an identifier

- Compiler:
  - Fix build reproducibility

# v3.0.0 (July 2025)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Language:
  - A **functional predicate** is a predicate that does not leave choice points
    for any of its calls. A functional predicate can have preconditions, eg
    `map` is functional if the higher order argument also is. Functional
    predicates (with preconditions) can be miscalled, in that case they behave
    as relations.
  - The matching operator used for input arguments is now also available as a
    builtin predicate named `pattern_match`.

- API:
  - New `Utils.ground_check` and `Utils.cmp_term` (already available as builtins)
  - Change `Constants.declare_global_symbol` takes an optional `variant` argument.

- Parser:
  - The `fprop` keyword is akin to `prop` but signals the predicate is functional
  - The `:functional` attribute flags `pred`icates as functional (equivalent to `func ...`).
  - Dedicated syntax for functional signatures:  
    `func name(comma_sep(types_of_inputs)* [-> comma_sep(types_of_outputs*)]`.
    Example: The signature of `map` is `func map list A, (func A -> B) -> list B`
  - New `[external] symbol name : type [= "variant"]` is a synonim of `type` and can be
    used to ascribe a type to a symbol. External symbols must be matched by
    a declaration in OCaml, and when the symbol is overloaded the variant
    label is used for the matching (additionally to the name).

- Compiler:
  - The type checker is in charge of resolving all symbols, overloaded or not,
    to a `Symbol.t` datatype that gathers the `Loc.t` where it is defined
    (and it can be defined at multiple places, e.g. OCaml + Elpi, or twice
    in Elpi). This data can be used to implement jump-to-def and the like in
    modern UIs.
  - The `determinacy_checker` statically analyzes whether a predicate labeled
    as functional adheres to its signature.
  - The elaboration of `{spilling}` has been moved to a dedicated file.
  - CHR rules are typechecked (finally)
  - Macros are typechecked. This paves the way to make them live in name
    spaces and possibly globally available, but it is not implemented yet.

- Runtime:
  - Builtin predicates now have a dedicated node when they are part of the
    Elpi language, i.e. Cut, And, Impl, RImpl, Pi, Sigma, Eq, Match, Findall,
    Delay.
  - Symbols part of the Elpi language (other than the builtins) also have
    a dedicated status, i.e. As, Uv, ECons, ENil although As and Uv do not
    have a dedicated node in the AST, while ENil and ECons do have it.

# v2.0.7 (January 2025)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Parser:
  - New `elpi:if version <name> <op> <ma>.<mi>.<p>`

- API:
  - New `Setup.init` takes a `?versions` dictionary to declare versions
    of external components
  - New `Utils.parse_version`

# v2.0.6 (December 2024)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Compiler:
  - Store timing info only optionally to restore build reproducibility
  - Fix collision between kinds and types in namespace handling

# v2.0.5 (December 2024)


Requires Menhir 20211230 and OCaml 4.13 or above.

- Parser:
  - Fix loc issues involving quotations

# v2.0.4 (November 2024)


Requires Menhir 20211230 and OCaml 4.13 or above.

- Type Checker:
  - Fix caching issue, units are now type checked every time they are processed

# v2.0.3 (November 2024)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Parser:
  - Fix parsing of infix `==>` so that `A,B ==> C,D` means `A, (B => (C,D))`
    as it is intended to be.


# v2.0.2 (November 2024)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Really fix tests on 32 bits systems

# v2.0.1 (November 2024)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Fix tests on 32 bits systems

# v2.0.0 (November 2024)

Requires Menhir 20211230 and OCaml 4.13 or above.

- Compiler:
  - Change the pipeline completely to make unit relocation unnecessary. Current
    phases are (roughly):
    1. `Ast.program` —[`RecoverStructure`]—> `Ast.Structured.program`
    2. `Ast.Structured.program` —[`Scope`,`Quotation`,`Macro`]—> `Scoped.program` (aka `API.Compile.scoped_program`)
    3. `Scoped.program` —[`Flatten`]—> `Flat.program`
    4. `Flat.program` —[`Check`]—> `CheckedFlat.program` (aka `API.Compile.compilation_unit`)
    5. `CheckedFlat.program` —[`Spill`,`ToDbl`]—> `Assembled.program`

    Steps 4 and 5 operate on a base, that is an `Assembled.program` being
    extended. `ToDbl` is in charge of allocating constants (numbers) for global
    names and takes place when the unit is assembled on the base. These
    constants don't need to be relocated as in the previous backend that
    would allocate these constants much earlier.
  - Change compilation units can declare new builtin predicates
  - Fix macros are hygienic
  - New type checker written in OCaml. The new type checker is faster,
    reports error messages with a precise location and performs checking
    incrementally when the API for separate compilation is used.
    The new type checker is a bit less permissive since the old one would
    merged together all types declaration before type checking the entire
    program, while the new one type checks each unit using the types declared
    inside the unit or declared in the base it extends, but not the types
    declared in units that (will) follow it.
  - Remove the need of `typeabbrv string (ctype "string")` and similar
  - New type check types and kinds (used to be ignored).

- API:
  - Change quotations generate `Ast.Term.t` and not `RawData.t`. The data
    type `Ast.Term.t` contains locations (for locating type errors) and
    has named (bound) variables and type annotations in `Ast.Type.t`.
  - New `Compile.extend_signature` and `Compile.signature` to extend a
    program with the signature (the types, not the code) of a unit
  - New `Ast.Loc.t` carries a opaque payload defined by the host application
  - Remove `Query`, only `RawQuery` is available (or `Compile.query`)

- Parser:
  - Remove legacy parser
  - New `% elpi:if version op A.B.C` and `% elpi:endif` lexing directives
  - New warning for `A => B, C` to be disabled by putting parentheses
    around `A => B`.

- Language:
  - New infix `==>` standing for application but with "the right precedence™",
    i.e. `A ==> B, C` means `A => (B, C)`.
  - New `pred` is allowed in anonymous predicates, eg:
    `pred map i:list A, i:(pred i:A, o:B), o:list B` declares that the first
    argument of `map` is a predicate whose first argument is in input and
    the second in output. Currently the mode checker is still in development,
    annotations for higher order arguments are ignored.
  - New attribute `:functional` can be passed to predicates (but not types).
    For example, `:functional pred map i:list A, i:(:functional pred i:A, o:B), o:list B`
    declares `map` to be a functional predicate iff its higher order argument is
    functional. Currently the determinacy checker is still in development, these
    annotations are ignored.
  - New `func` keyword standing for `:functional pred`. The declaration above
    can be shortened to `func map i:list A, i:(func i:A, o:B), o:list B`.
  - New type annotations on variables quantified by `pi` as in `pi x : term \ ...`
  - New type casts on terms, as in `f (x : term)`
  - New attribute `:untyped` to skip the type checking of a rule.

- Stdlib:
  - New `std.list.init N E L` builds a list `L = [E, ..., E]` with length `N`
  - New `std.list.make N F L` builds the list `L = [F 0, F 1, ..., F (N-1)]`
  - New `triple` data type with constructor `triple` and projections `triple_1`...

- Builtins:
  - Remove `string_to_term`, `read`, `readterm`, `quote_syntax`

- REPL:
  - Remove `-no-tc`, `-legacy-parser`, `-legacy-parser-available`
  - New `-document-infix-syntax`


# v1.20.0 (September 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

- Language:
  - attribute `:remove` to remove a clause from the program

- Compiler:
  - Build the index at assembly time, rather than optimization time.
    This makes compilation slower, but startup faster.
  - Adding clauses before the type/mode declaration of a predicate
    is now forbidden, since they are immediately inserted in the index
    and the type/mode declaration can change the index type

# v1.19.6 (August 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

- Runtime:
  - Fix bug in unification code for "automatic intro" (as in the intro tactic)
    of UVar arguments

# v1.19.5 (July 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

- Compiler:
  - Improve performance of separate compilation
  
- CHR:
  - Syntax extension for constraint declaration.
  - This aims to avoid the `overlapping` clique error
  - Example: `constraint c t x ?- p1 p2 { rule (Ctx ?- ...) <=> (Ctx => ...) }`
  - `c`, `t` and `x` are the symbols which should be loaded in the rule of the
    constraint and should be considered as symbols composing the context (`Ctx`)
    under which `p1` and `p2` are used.

# v1.19.4 (July 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

- Stdlib:
  - Add `once` predicate

- Build:
  - New `make tests PROMOTE=true`

- Parser:
  - Change purge `_build/xxx` from paths once files are resolved in order
    to have locs point to the sources and not their copy in `_build`

# v1.19.3 (June 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

- Linter:
  - Fix regex for linearity check, `Foo_Bar` was silently ignored for
    linearity purpose

- Parser:
  - Fix error message for named quotation

- Runtime:
  - Fix missing restriction

# v1.19.2 (June 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

- Builtins:
  - Add `choose`, `min`, `max`, `fold` and `partition` methods to OCaml sets
  - Add `fold` method to OCaml maps

- Stdlib:
  - Fix first argument of `std.rev` is in input

- Runtime:
  - Fix discrimination tree retrieval

# v1.19.1 (June 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

Language:
  - New `:index (<arg-spec>) "index-type"` where the index type can be
    Map, Hash or DTree

Runtime:
  - Fix performance regression due to the fix to relocation in unification
    introduced in 1.19.0
  - New list flattening in DTree index, that is term `app [t1,t2,t3]`
    is indexed using the same DTree space/depth of term `app t1 t2 t3`
    
# v1.19.0 (May 2024)

Language:
  - Change CHR syntax now accepts any term in eigen variables position `E` in
    sequent `E : _ ?- _`. Meaningful terms are lists or unification variables
  - Change CHR eigen variables are a list of names (used to be an integer)

Runtime:
  - Fix CHR relocation/scope-checking for new goals
  - Fix relocation error in unification on non-linear patterns with locally
    bound variables

# v1.18.2 (January 2024)

Requires Menhir 20211230 and OCaml 4.08 or above.

Language:
  - Change indexing for multiple arguments is now based on discrimination trees
  - Change `:index` acecpts an optional string to force `"Hash"` based indexing

API:
  - Change `clause_of_term` accepts a ``` `Replace ``` grafting directive

# v1.18.1 (December 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.

Parser:
  - Remove legacy parsing engine based on Camlp5

API:
  - New `RawQuery.compile_ast`, lets one set up the initial state in which the
    query is run, even if the query is given as an ast.
  - New `solution.relocate_assignment_to_runtime` to pass a query result
    to another query
  - New `BuiltInPredicate.FullHO` for higher order external predicates
  - New `BuiltInPredicate.HOAdaptors` for `map` and `filter` like HO predicates
  - New `Calc.register` to register operators for `calc` (aka infix `is`)

Library:
  - New `std.fold-right`

Runtime:
  - New clause retrieval through discrimination tree. This new index is enabled
    whenever the `:index` directive selects only one argument  with a depth `> 1`.

# v1.18.0 (October 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

API:
  - Change `Setup.init` takes a `?state`, `?quotations` and `?hooks` descriptors so that
    each `elpi` handle is completely independent.
  - Change `State.declare` is deprecated in favor of `State.declare_component`
  - New `State.declare_component` like `State.declare` but takes a `~descriptor`
  - New `State.new_state_descriptor`
  - Change `Quotations.register_named_quotation` now takes a `?descriptor`
  - Change `Quotations.set_default_quotation` now takes a `?descriptor`
  - Change `Quotations.declare_backtick` now takes a `?descriptor`
  - Change `Quotations.declare_singlequote` now takes a `?descriptor`
  - New `Quotations.new_quotations_descriptor`
  - Change `RawData.set_extra_goals_postprocessing` now takes a `?descriptor`
  - New `RawData.new_hoas_descriptor`

# v1.17.4 (October 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

Parser:
  - Fix location handling (used to ignore the char count of the initial loc)

# v1.17.3 (September 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

Builtins:
  - Change `unix.process` really disabled on OCaml 4.12

# v1.17.2 (September 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

Builtins:
  - Change `unix.process` disabled on OCaml 4.12

# v1.17.1 (September 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

Builtins:
  - New `unix.process` datatype and `unix.process.open/close` APIs

# v1.17.0 (July 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

Compiler:
  - Improve performance of separate compilation, in particular
    extending a program with more clauses. This change may
    break existing code which accumulates units containing
    the spilling of a predicate *before* the unit declaring
    the predicate signature.

Parser:
  - Fix error message on unexpected keyword (was wrongly assuming the
    keyword was `)` misleading the user)

Builtins:
  - Change type of `declare_constraint` to `any -> any -> variadic any prop`
    making it explicitly take at least two arguments

Trace browser:
  - Fix elaboration of CHR rule with no condition

# v1.16.10 (May 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Elpi:
  - New attribute `:replace` which replaces a named clause by an unnamed one

Trace browser:
  - Fix display of rule applied after failures

# v1.16.9 (March 2023)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Trace browser:
  - Fix CHR trace elaboration in case no rule applies

# v1.16.8 (November 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Dependencies:
  - yojson 2.x, hence atd 2.10

# v1.16.7 (October 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Tests:
  - Fix trace elaboration reference files

# v1.16.6 (October 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- API:
  - Fix `FlexData.Elpi.make` when called with a name after compilation is over
  - Fix `RawQuery.mk_Arg` can only be called at compile time
  - Fix anomaly in `Query.compile`

- Trace:
  - Fix printing of clauses

- Doc:
  - New setup based on Sphinx (still no extra contents)

# v1.16.5 (July 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Apis in the Builtin module:
  - New `string_set`, `int_set` and `loc_set` conversions
  - New `ocaml_set_conv` giving both the declarations and the conversion for the
    provided OCaml `Set` module

# v1.16.4 (July 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Tace Elaborator:
  - Fix generation and elaboration of incomplete traces

- Trace:
  - New command line syntax `file://` and `tcp://` to disambiguate
    `host:port` on windows (old syntax still supported)

# v1.16.3 (June 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Fix compilation on OCaml 5.0.0

# v1.16.2 (June 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Trace Elaborator:
  - Fix json encoding of utf8 characters
  - Fix runtime_id does not necessarily start at 0

# v1.16.1 (June 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Tests:
  - Fix temp file creation for trace testing

# v1.16.0 (June 2022)

Requires Menhir 20211230 and OCaml 4.08 or above.
Camlp5 8.0 or above is optional.

- Parser:
  - Change the character count in the locations is now referring to the
    beginning of the text, and not the end
- Printer:
  - Fix regression not putting parentheses correctly around some applications
- Doc:
  - Clarify `InOut` and `ioarg` doc in the API file
- Trace:
  - New `src/trace.atd` data type description for traces
  - New `src/trace_atd.ts` read/write the trace in `TypeScript`
  - New `elpi-trace-elaborator` tool to turn raw traces into cards to be
    displayed by a GUI. Work is in progress on the `elpi-lang` VS Code
    extension.
  - Change the raw trace as output by the runtime is way more regular w.r.t.
    what is printed when a rule, or a built in rule/predicate is run, also
    the runtime_id attribute is now correctly set in all trace objects
  - Fix the trace file is generated only once the trace is complete, so that
    tools can watch for the file creation reliably

# v1.15.2 (April 2022)

Requires Menhir 20211230 and OCaml 4.07 or above.
Camlp5 8.0 or above is optional.

*warning: The parser used by default is not backward compatible with 1.14.x*

- Parser:
  - Change `pred foo i:A o:B` is valid, `pred foo i:A o :B` is not. This
    change restores backward compatibility of existing code.

# v1.15.1 (April 2022)

Requires Menhir 20211230 and OCaml 4.07 or above.
Camlp5 8.0 or above is optional.

*warning: The parser used by default is not backward compatible with 1.14.x*

- Build:
  - Change legacy parser not built by default
  - New `make config LEGACY_PARSER=1` to enable it
  - New opam package `elpi-option-legacy-parser` to install elpi with
    the legacy parser enabled 

- Parser:
  - Fix missing infix `&` (synonym of `,`)
  - New comma separator is optional in `pred` declarations, eg
    `pred i:A o:B.` is valid syntax

# v1.15.0 (April 2022)

Requires Menhir 20211230 and OCaml 4.07 or above.
Camlp5 is now optional.

*warning: The parser used by default is not backward compatible*

- Parser:
  - New parser based on Menhir
    + The grammar is not extensible anymore; token families are used to provide
      open ended infix symbols, see the [documentation](src/parser/README.md)
    + Custom error messages suggesting examples with a valid syntax
    + Faster on large files
  - Old parser available via `-legacy-parser`
    + Only compiled when `camlp5` is available
    + Supports `infix` and similar mixfix directives

- API:
  - `Parse.goal_from_stream` -> `Parse.goal_from`
  - `Parse.program_from_stream` -> `Parse.program_from`
  - `Parse.resolve_file` now takes an `~elpi` argument
  - `Setup.init` resolver argument takes a `~unit` instead of `~file`
  - `Setup.init` takes `?legacy_parser`
  - `Setup.legacy_parser_avaiable`
  - `Pp.query` -> `Pp.program` and `Pp.goal`

- REPL:
  - New `-parse-term`
  - New `-legacy-parser`
  - New `-legacy-parser-available`
  - Removed `-print-accumulated-files`

# v1.14.3 (March 2022)

- Tests:
  - `test.exe` understands `--skip-cat`
  - `make tests` understands `SKIP` for the categories to skip

# v1.14.2 (March 2022)

- Dependencies:
  - bump camlp5 to >= 8.0

# v1.14.1 (February 2022)

- Runtime:
  - Fix unification dealing with a deep `AppArg` (regression in 1.14.0)
  
# v1.14.0 (February 2022)

- Runtime/FFI:
  - Fix handling of eta expanded unification variables. Many thanks to
    Nathan Guermond for testing this tricky case.
  - Change `Rawdata.Constants.eqc` to a builtin
  - Fix `Rawdata.Constants.cutc` has always been a builtin
  - Fix compatibility with OCaml multicore, no more `PtrMap`
- API:
  - New `FlexibleData.WeakMap` to link unification variables with host
    data based on OCaml's `Ephemeron`
  - Change `Conversion.extra_goals` is now an extensible data type with one
    standard constructor `Conversion.Unify` taking two terms
  - New `RawData.set_extra_goals_postprocessing` can be used to
    post process the extra goals generated by an FFI call.
    One has to translate extensions to the `extra_goals` datatype to
    `RawData.RawGoal` (or `Conversion.Unify`), but can also take global
    actions like cancelling out useless or duplicate goals
  - Change `Setup.init` to take in input a `~file_resolver` rather than a list
    of `~paths` and a `~basedir`. A custom file resolver can use some logic
    from the host application to find files, rather than an hardcoded one
  - New `Parse.std_resolver` building a standard resolver (based on paths)
  - Change signature of `Parse.resolve_file` making `?cwd` explicit
- Library:
  - Better error messages in `std.nth`
  - `declare_constraint` is now `variadic any prop`, so that one can pass
    variables of different types as keys for the constraint. A list of variables
    (of the same type) is still supported.

# v1.13.8 (November 2021)

- Build:
  - link `camlp5.gramlib` as part of `elpi.cmxs` so that the plugin can be
    loaded via findlib.

# v1.13.7 (July 2021)

- Compiler:
  - Fix bug in spilling when the spilled expression generates more than one
    argument.

# v1.13.6 (June 2021)

- API:
  - Fix `std.findall` is now calling a builtin which is able to produce
    solutions which contain eigenvariables and uvars as well.
  - `loc` is now printed using `/` as a path separator also on Windows
  - `loc.fields` to project a `loc` into the file, line, etc...

# v1.13.5 (May 2021)

- API:
  - New `prune` which can be used to prune a unification variable
  - New `distinct_names` which checks if a list of arguments is in the pattern
    fragment

# v1.13.4 (May 2021)

- FFI: new `ioargC_flex` which considers flexible terms as Data

# v1.13.3 (May 2021)

- Bugifx: keep the state component `while_compiling` even when execution is
  over, since the API to allocate a new Elpi uvar needs it and Coq-Elpi may
  call this API while translating the solution to Coq

# v1.13.2 (May 2021)

- Build:
  - drop ppxfindcache
  - relax dependency on ocaml-migrate-parsetree

# v1.13.1 (April 2021)

- API:
  - New `gc.get` and `gc.set` for reading and writing GC settings
  - New `gc.minor`
  - New `gc.major`
  - New `gc.full`
  - New `gc.compact`
  - New `gc.stat`
  - New `gc.quick-stat`
  - New `min` and `max` operators for the `is` builtin, they work on
    `int` and `float`
  - Rename `rex_match` -> `rex.match`
  - Rename `rex_replace` -> `rex.replace`
  - Rename `rex_split` -> `rex.split`
  - Rename `counter` -> `trace.counter`
- FFI:
  - New `Builtin.unspec` type to express optional input

# v1.13.0 (Feb 2021)

- API:
  - Fix `open_append` was messing up file permissions
  - New `Parse.resolve_file` to find where the parser would find (or not) an
    accumulated file
  - Change signature of `Compile.unit`, `Compile.assemble` and `Compile.extend`
    and improve their implementation. Units are now smaller and link/relocate
    faster (making `~follows` not worth it)
- CI:
  - Switch to Github actions and avsm/setup-ocaml. Now testing on Linux, MacOS
    and Windows. Artifacts produce binaries for all platforms and a benchmarks
    plot.
- Library:
  - New `if2`
  - New `std.map-ok`
  - New `std.fold-map`
  - New `std.intersperse`
  - New `std.omap`
  - New `std.take-last`
  - New `std.string.concat`

## v1.12.0 (Nov 2020)

- FFI:
  - `RawOpaqueData.cin` now returns a term and takes `constants` into account.
    Whenever a value is represented with a named constant, the API grants that:
    - the value is embedded using that constant
    - that constant is read back to the original value
- API:
  - New `Compile.extend` to (quickly) add clauses to a program
  - New argument `?follows:program` to `Compile.unit` to have the unit
    be compiled using the very same symbol table (no new symbols can be
    declared by the unit in this case)
- Library:
  - rename `map2_filter` -> `map2-filter`
  - new `map-filter`
- Build:
  - use md5 (OCaml's digest) instead of sha1 (external utility)

## v1.11.4 (Aug 2020)

- do not rely on /bin/bash in Makefile (helps on nix and freebsd)

## v1.11.3 (Aug 2020)

- ppxfindcache: use `shasum` instead of `sha1sum`
- Parser: print file names in a VScode friendly way
- Fix opam package dependency on camlp5 and ppxlib
- Fix output of `-print*` options to the `elpi` command line utility
- New builtin `rex_split` (like OCaml's `Str.split`)

## v1.11.2 (May 2020)

- Nicer error message when compiling an applied spilling expression
- Fix opam package
- Trace: print locations in VScode friendly way

## v1.11.1 (May 2020)

- Fix to the opam file, ppxlib is required to be >= 0.12.0 and
  ocaml-migrate-parsetree >= 1.6.0. Moreover we disable tests on Alpine linux
- Print locations in such a way that VScode can understand then, and click jump
  to type errors

## v1.11.0 (May 2020)

- Builtin:
  - `var` now accepts 3 arguments, as `constant` and `name`.

- Trace:
  - output facilities: json and tty on both files and network sockets
  - trace messages to link goals to their subgoals
  - spy points categorized into `user` and `dev`
  - all trace points were revised and improved
  - port to ppxlib

- Build system:
  - minimal build dependencies are now: camlp5 ocamlfind dune re
  - cache ppx output in .ml format in `src/.ppcache` that Elpi can be buildt
    without `ppx_deriving.std` and `elpi.trace.ppx` using a new tool in
    `ppxfindcache/`
  - vendor a copy of `ppx_deriving_runtime` (suffix `_proxy`) to be used when
    `ppx_deriving` is not installed
  - generate custom `merlinppx.exe` for `src/` and and patch `.merlin` file so
    that one can have decent merlin support
  - make target `test-noppx` to compile on an alternative opam switch

## v1.10.2 (February 2020)

- Builtin:
  - occurs now accepts arguments of different types

- API:
  - expose beta reduction on raw terms

## v1.10.1 (February 2020)

- make API.Builtin_checker module public so that third parties can reuse the
  source

## v1.10.0 (February 2020)

- Compiler:
  - large refactoring to separate the table of global (statically initialized)
    symbols, the table of symbols of a program being compiled and the table
    of symbols used at runtime.
  - API for separate compilation.

- API:
  - Setup.init now returns a handle to an elpi instance to be passed to
    many other APIs.
  - New APIs Compile.unit and Compile.assemble for separate compilation.
  - Constants.from_stringc and Constants.mk*S API removed in favor for
    Constants.declare_global_symbol (to be used in module initialization code).


## v1.9.1 (January 2020)

- Tests:
  - Fix testing framework on runners pre 1.9.0.

- Parser:
  - Line numbers after quotations were wrong, since `\n` inside
    quotations were not taken into account.

- Typing:
  - Name alias abbreviations are not refolded in error messages.
    Eg. `typeabbrev x int` does not take over `int`, while
    `typeabbrev x (list int)` does over `list int`.
  - Fix type abbreviation refolding, was not working on some cases.

- Stdlib:
  - Fix `is` function `int_of_string` to do what it says
  - New `is` function `rhc : string -> int` computes the inverse of `chr`

## v1.9.0 (January 2020)

- Typing:
  - `typeabbrev` declarations are now taken into account and unfolded
    by the compiler. The type checker refolds abbreviations
    when printing error messages with the following caveat: when two type
    abbreviations can be refolded the last declared one wins.

- Compiler:
  - `@macro` are no more accepted in types, since `typeabbrev` provides the
    same functionality.
  - fix clash between builtin names and type names
  - `accumulate` is idempotent: accumulating the same file a second time
    has no effect.

- FFI:
  - built in predicate are allowed to not assign (not produce a value) for
    output and input-output arguments.
  - input-output arguments are forced to be `Conversion.t` of type `'a ioarg`,
    and recommended to wrap any nested type not able to represent variables
    in `ioarg`. Eg `int option` should be `int ioarg option ioarg`. In this
    way one can safely call these builtins with non-ground terms, such as
    `some _`, for example to assert the result is not `none` but without
    providing a ground term such as `some 3`.
  - `MLData` declarations for `OpaqueData` are no more named using a macro
    but rather using a type abbreviation. This can break user code. The fix
    is to substitute `@myopaquetype` with `myopaquetype` everywhere.

- Stdlib:
  - `diagnostic` data type to be used as an `ioarg` for builtins that can fail
    with a relevant error message. On the ML side one can used `Elpi.Builtin.mkOK`
    and `Elpi.Builtin.mkERROR "msg"` to build its values.
  - `std.assert-ok!`, `std.forall-ok`, `std.do-ok!`, `std.lift-ok` and
    `std.while-ok-do!` commodity predicates.
  - All operators for `calc` (infix `_ is _`) now come with a type declaration.

## v1.8.0 (October 2019)

- Bugfix:
  - `shorten foo.{ bar }.` when `foo.bar` is a builtin used to be miscompiled.
  - `elpi-typechecker.elpi` now correclty stops printing warnings after it
    printed 10 (used to stop after he processed 10, that may not be the same
    thing, since some warnings are suppressed).

- Parser:
  - Interpret `-2` (with no space) as the negative `2` not as the constant `-2`.
    This way `X is 3 - 2` and `Y is 3 + -2` are both valid.

- FFI:
  - `OpaqueData` now requires a ternary comparison, not just equality.

- Stdlib:
  - new data type `cmp` for ternary comparison.
  - `std.set` and `std.map` now based on ternary comparison.

- Builtin:
  - `cmp_term` giving an order on ground terms.
  - `ground_term` to check if a term is ground.

## v1.7.0 (September 2019)

- Parser:
  - Tolerate trailing `,` in lists, eg `[1,2,3,]` is now parsed as `[1,2,3]`.
  - Error if the input of `Parse.goal_from_string` contains extra tokens
  - Binary conjunction `&` is now turned on the fly into the nary one `,`.

- Bugfix:
  - Nasty bug in pruning during higher order unification, see #36.
  - `Discard` is now considered a stack term, and is turned into an
    unification variable on heapification.
  - `API.RawData.look` now expands `UVar` correctly

- Stdlib:
  - `set` and `map` for arbitrary terms equipped with an order relation.
    Based on the code of OCaml's `Map` and `Set` library.
  - New API `map.remove` for maps on builtin data.
  
- FFI:
  - New `ContextualConversion` module and `ctx_readback` type. In an FFI call
    one can specify a readback for the hypothetical context that is run once
    and its output is give to the ML code instead of the "raw" constraints and
    hyp list.
  
- API:
  - Commodity functions in `Elpi.Builtin` to export as built-in
    OCaml's `Set.S` and `Map.S` interfaces (the output of `Set.Make`
    and `Map.Make`). All data is limited to be a closed term.
  - `Constants.andc2` was removed
  - `FlexibleData.Elpi.make` takes no `~lvl` argument (it is always `0`)
  - `RawData.view` no more contains `Discard` since it is not an heap term

- Misc:
  - Pretty printer for unification variable made re-entrant w.r.t. calls to the
    CHR engine (used to lose the mapping between heap cells and names)
  - Pretty printer for solution abstracted over a context (part of the solution). In this
    way the result can be printed correctly even if the runtime has been destroyed.
  - Default paths for finding `.elpi` files fixed after the switch to dune
  - A few more tests regarding unification, data structures and performance

## v1.6.0 (July 2019)

- Builtin:
  - `same_term` (infix `==`) for Prolog's non-logical comparison (without
    instantiation).
  - `set` and `map A` (`A` only allowed to be a closed term) on
    `string`, `int` and `loc` keys.

- Compiler:
  - provide line number on error about duplicate mode declaration
  - elpi-checker is faster and bails out after 10 seconds

- FFI:
  - allow `AlgebraicData` declarations to mix `M` and `MS` constructors
  - `Conversion.t` for closed terms (no unification variable and no variables
    bound by the program)

- Tests:
  - typecheck all tests and measure type checking time

## v1.5.2 (July 2019)

- Test suite: ship elpi-quoted_syntax.elpi

## v1.5.1 (July 2019)

- Test suite: print the log of the first failure to ease debugging on third
  party CI.

## v1.5.0 (July 2019)

Elpi 1.5 requires OCaml 4.04 or newer

- REPL:
  - type errors are considered fatal, pass `-no-tc` to skip type checking.
  - use dune subst in order to implement `-version` flag to the command line
    utility.

- Runtime:
  - reset unification variables names map at each execution. This makes
    the names of variable printed in a reproducible way across executions.

- FFI:
  - `readback` is now as powerful as `embed` and can generate extra goals. The
    two types are now dual.

## v1.4 (June 2019)

Elpi 1.4 requires OCaml 4.04 or newer

- Sources and build: Switch to dune, with a little make base wrapper.
  As a result of dune wrapping the library all sources are renamed from
  `elpi_x.ml` to `x.ml`, and each module `Elpi_X` is now available as `Elpi.X`.
  In particular clients must now use `Elpi.API` and `Elpi.Builtin`.

- FFI:
  - `Conversion.TypeErr` now carries the depth at which the error is found, so
    that the term payload can be correctly printed.
  - Built in predicates are allowed to raise TypeErr in their body
  - `BuiltInPredicate.Full` now returns a list of `extra_goals`, exactly as
    `Conversion.embed` does making conversion code easy to call in the body
    of a predicate.

## v1.3 (June 2019)

Elpi 1.3 requires OCaml 4.04 or newer

- API:
  Major reorganization: The Extend module has gone; the module structure is flat
  and ordered by complexity. Most modules are named after the kind of data they
  let one represent. Eg `AlgebraicData`, `OpaqueData`, `FlexibleData` or for low
  level access `RawOpaqueData` or `RawData` for naked terms.

- FFI:
  - `RawData.mkAppL` and `RawData.mkAppSL` handy constructors
  - `custom_state` renamed `state`
  - No more `solution` in the type of builtin predicates but rather
    `constraints` and `state` explicitly
  - Only one type of extensible state to that the same code can be used to
    generate the query at compile time and convert data at run time
  - Unify `MLCData` and `MLADT` into `MLData`
  - `AlgebraicData.t` supports `C` for containers, so that one can model
      ```ocaml
      type t = A | B of list t
      ```
    as
      ```ocaml
      K("a", N, ..
      K("b",(C ((fun x -> list x),N)), ..
      ```
  - new `FlexibleTerm.Elpi.t` and `FlexibleTerm.Map` to represent Elpi's 
    unification variables and keep a bijective map between them and any host
    application data.
  - `RawData.term` contains no more `UVar`, `AppUVar`, `Arg` and `AppArg` but
    only `UnifVar of FlexibleTerm.Elpi.t * term list`.
  - Simple GADT for describing a query. When a query is built that way, the
    `solution` contains an output field holding data of the type described by
    the query.

- Library:
  - replace `mode (std.mem i i)` with `(std.mem i o)`: member can be assigned
  - separate `std.mem!` and `std.mem`

## v1.2 (April 2019)

Fix:
 - equality up-to eta on rigid terms (used to work only on flexible terms)
 - `expand_*` in charge of putting unification variables in canonical form
   was sometimes omitting some lambdas in one of its outputs

Language:
 - `shorten` directive to give short names to symbols that live in namespaces,
   e.g.  `shorten std.{ rev }` lets one write `rev` instead of `std.rev`
 - spilling understands implication and conjunction, e.g. `g { h => (a, f) }`
   becomes `(h => (a, f X)), g X`
 - syntax of `.. as X` to bind subterms in the head of a clause changed
   precedence. In particular `lam x\ B as X` binds `lam x\ B` to `X`
   (instead of just `B`, as it was the case in previous versions)
 - `:index(...)` attribute for predicates to select which argument(s) should be
   indexed and at which depth. Multi-argument indexing and deep-indexing are
   based on unification hashes, see [ELPI.md](ELPI.md) for more details
   
Library:
 - predefined types:
   + `bool` with `tt` and `ff`
   + `option A` with `none` and `some A`
   + `pair A B` with `pr A B`, `fst` and `snd`
 - predefined control structure:
   + `if C T E`

 - standard library (taken from coq-elpi) in the `std` namespace.
 
   Conventions:
   + all errors are signalled using one of the following two symbols
     that can be overridden by grafting clauses to hide them,
     namely `fatal-error` and `fatal-error-w-data`
   + the `!` suffix is for (variants) of predicates that generate only the
     first solution
   + all predicates have mode declarations that follow their functional
     interpretation; variants keeping the relational interpretation are named
     using the `R` suffix
     
   Symbols: `debug-print`, `ignore-failure!`, `assert!`, `spy`, `spy!`,
   `unsafe-cast`, `length`, `rev`, `last`, `append`, `appendR`, `take`, `drop`,
   `drop-last`, `split-at`, `fold`, `fold2`, `map`, `map-i`, `map2`,
   `map2_filter`, `nth`, `lookup`, `lookup!`, `mem`, `exists`, `exists2`,
   `forall`, `forall2`, `filter`, `zip`, `unzip`, `flatten`, `null`, `iota`,
   `flip`, `time`, `do!`, `spy-do!`, `any->string`, `random.init`,
   `random.self_init`, `random.int`

   While the predicates in the library are reasonably tested, their names and
   name spaces may change in the future, e.g. a specific name space for
   list related code may be created (as well for strings, debug, etc).

Builtin:
 - `name` is now typed as `any -> variadic any prop` to support the following
   two use cases:
   + `name T` succeeds if `T` is an eigenvariable (even if it is applied)
   + `name T HD ARGS` relates `T` (an applied eigenvariable) to its head
     and arguments (as a list):
     `pi f x y\ name (f x y) f [x,y]`
 - new builtin `constant` working as `name` but for non-eigenvariables
 - `halt` now accepts any term, not just strings
 - `getenv` is now typed as `string -> option string` and never fails.
   The old semantics can be obtained by just writing `getenv Name (some Value)`

API:
 - new data type of locations in the source file: `Ast.Loc.t`
 - exception `ParseError(loc, message)` systematically used in the
   parsing API (no more leak of exceptions or data types from the internal
   parsing engine, i.e. no more `NotInProlog` or `Stream.Error` exceptions)
 - type of quotations handlers changed: they now receive in input the location
   of the quoted text in order to be able to locate their own parsing errors
 - simplified term constructors:
   + `mkConst` split into `mkGlobal` and `mkBound`
   + variants with trailing `S` taking a `string` rather than
     a global constant, e.g. `mkAppS`, `mkGlobalS`, `mkBuiltinS`
   + `mkBuiltinName` removed (replace by `mkBuiltinS`)
   + constant `spillc` exported: one can not build a term such as `f {g a}`
     by writing `mkAppS "f" (mkApp spillc (mkAppS "g" (mkGlobalS "a") []) []`
 - FFI:
   + `to_term` and `of_term` renamed to `embed` and `readback` and made
     stateful.  They can access the state, the hypothetical context and the
     constraint store (exactly as `Full` ffi builtins do) and can return an
     updated state. Moreover `embed` can generate new goals (eg declaration of
     constraints) so that data that requires companion constraints fits the
     capabilities of the FFI (no need to simulate that by using a `Full`
     predicate with arguments of type `any`, as coq-elpi was doing)
   + Arguments to builtin predicates now distinguish between
     - `In` ML code must receive the data, type error is the data cannot
       be represented in ML
     - `Out` ML code received `Keep` or `Discard` so that it can
       avoid generating data the caller is not binding back
     - `InOut` ML code receives `Data of 'a` or `NoData`. The latter case is
       when the caller passed `_`, while the former contains the actual data
   + In the declaration of a data type for the FFI, the `ty` field is no more a
     string but an AST, so that containers (eg `val list : 'a data -> 'a list
     data`) can more easily generate the composite type
   + New GADT to describe simple ADTs (with no binders)

Compiler:
 - handling of locations for quotations
 - better error reporting: many errors now come with a location

REPL:
 - more structure in the output of `--help` including hints for the tracing
   options
 - new option `-print-passes` to debug the compiler

Test Suite:
 - rewritten using more OCaml & Dune and less bash & make. Requires
   `dune`, `cmdliner` and `ANSITerminal` in order to build

## v1.1.1 (October 2018)

Fix:
 - `beta` was not calling `deref_*` in all cases, possibly terminating reduction
   too early (and raising an anomaly)

## v1.1 (September 2018)

Language:
 - CHR semantics conformed to the "revised operational semantics", that is
   roughly the following:
   - 1 for each active constraint (just declared via declare_constraint)
     - 2 for each rule
       - 3 for each position j of the active constraint (from 0 to n)
         - 4 for each permutation of constraints having the active at j
           - 5 try apply the rule
             - 6 remove constraints to be removed from
                 the current set of permutations and the set of
                 active or passive constraints
                 
   In Elpi 1.0 loops 3 and 2 were swapped (by mistake)
   
 - CHR keys refined. In `declare_constraints C KEYS`:
   + `KEYS` must be a list of variables (no more special case `KEYS = Var`)
   + `KEYS` = `[_,...]` labels the constraint with the unique variable `_`.
     In other words `_` is a master key one can use to label constraints
     that share no other variable and that have to be combined together.
     The master key will never be assigned, hence it does not count for
     resumption
   + `KEYS` = `[]` is accepted with the following meaning: constraints with
     no key are never resumed automatically and are never combined with other
     constraints

Builtin:
 - `halt` is now typed as `variadic string prop` and the strings passed
   are printed when the interpreter halts

Aesthetic:
 - bound variables are now printed as `c0, c1, ...` instead of `x0, x1, ...`
   to avoid ambiguity with `X0, X1, ...` on small/far-away screens

API changes:
 - rename:
   + `custom_constraints` -> `state` (record field)
   + `syntactic_constraints` -> `constraints` (type)
   + `CustomConstraint` -> `CustomState` (module)
 - add:
   + `StrMap` and `StrSet`: expose `pp` and `show`
 - alias:
   + `Data.Extend.solution` ~ `Data.solution` (cast: `Data.Extend.of_solution`)

Compilation:
 - require re >= 1.7.2 (the version introducing `Re_str` -> `Re.str`)

Misc:
 - improved some error messages, minor fixes to elpi-checker

## v1.0 (April 2018)
Second public release, developed in tandem with coq-elpi and matita-elpi.

The programming language features syntactic constraints (suspended goals) and
a meta language (inspired by CHR) to manipulate the constrain store.

There is an API for clients letting one drive the interpreter and
extend the set of built-in predicates, register quotations and
anti-quotations, etc.

The software is now built using findlib into a library.
The standalone interpreter is just a regular client of the API.

## LPAR 2015 (Jul 12, 2015)
First public release accompanying the paper 
[ELPI: fast, Embeddable, λProlog Interpreter](https://hal.inria.fr/hal-01176856/)
