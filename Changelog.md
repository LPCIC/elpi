## Version 1.2 (... 2019)

Language:
 - syntax of `.. as X` to bind subterms in the head of a clause changed
   precedence. In particular `lam x\ B as X` binds `lam x\ B` to `X`
   (instead of just `B`)
 - spilling understands implication and conjunction, e.g. `g { h => (a, f) }`
   becomes `(h => (a, f X)), g X`
   
Library:
 - predefined types:
   + `bool` with `tt` and `ff`
   + `option A` with `none` and `some A`
   + `pair A B` with `pr A B`

Builtin:
 - `name` is now typed as `any -> variadic any prop` to support the following
   two use cases:
   + `name T` succeeds if `T` is an eigenvariable (even if it is applied)
   + `name T HD ARGS` relates `T` (an applied eigenvariable) to its head
     and arguments (as a list):
     `pi f x y\ name (f x y) f [x,y]`
 - new builtin `constant` working as `name` but for non-eigenvariables
 - `halt` now accepts any term, not just strings

API:
 - new data type of locations in the source file
 - exception ParseError(location, message) systematically used in the
   parsing API (no more leak of exceptions or data types from the internal
   parsing engine, still camlp5 for now)
 - type of quotations handlers changed: they now receive in input the location
   of the quoted text in order to be able to locate their own parsing error
   messages
 - simplified term constructors:
   + `mkConst` split into `mkGlobal` and `mkBound`
   + variants with trailing `S` taking a `string` rather than
     a global constant, e.g. `mkAppS`, `mkGlobalS`, `mkBuiltinS`.
     `mkBuiltinName` got removed
 - FFI:
   + `to_term` and `of_term` are now stateful conversion functions, that is they
     see the state, hypothetical context and constraint store (as `Full` ffi builtins
     do) and can return an updated state
   + ffi arguments can now be `Data | Flex | Discard | OpaqueData`, the latter
     avoiding converion when the builtin is not bi-directional (e.g. cannot use
     an argument marked as output, he just imposes an equality on it)
   + `ty` is no more a string but an AST

Compilation:
 - handling of locations for quotations

Fix:
 - `expand_*` in charge of putting unification variables in canonical form
   was sometimes omitting some lambdas in one of its outputs
 - equality up-to eta on rigid terms (used to work only on flexible terms)

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
