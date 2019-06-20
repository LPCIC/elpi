## Version 1.4 (June 2019)

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

## Version 1.3 (June 2019)

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

## Version 1.2 (April 2019)

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

## Version 1.1.1 (October 2018)

Fix:
 - `beta` was not calling `deref_*` in all cases, possibly terminating reduction
   too early (and raising an anomaly)

## Version 1.1 (September 2018)

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

## Version 1.0 (April 2018)
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
