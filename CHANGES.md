## v1.9.1 (January 2020)

- Tests:
  - Fix testing framework on runners pre 1.9.0.

- Parser:
  - Line nubers after quotations were wrong, since `\n` inside
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
    is to substitutie `@myopaquetype` with `myopaquetype` everywhere.

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
