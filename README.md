[![Build Status](https://travis-ci.org/LPCIC/elpi.svg?branch=master)](https://travis-ci.org/LPCIC/elpi)
# ELPI

ELPI implements a variant of λProlog enriched with Constraint Handling Rules.

ELPI is a research project aimed at providing a programming platform
for the so called *elaborator* component of an interactive theorem prover.
ELPI stands for Embeddable Lambda Prolog Interpreter, and indeed it is
designed to be easily embedded into larger softwares 
as Coq or Matita.

ELPI is free software released under LGPL vesion 2.1 or above.

### How to install ELPI

ELPI is developed under Linux and is known to also work on MacOSX.
The simplest way is to use [OPAM](http://opam.ocaml.org/) and type
```
opam install elpi
```
This command gives you the command line tool `elpi` as well as the findlib
`-package elpi` switch.

To install the development version of elpi directly from github
you can type
```
opam pin add elpi https://github.com/LPCIC/elpi.git
```
You can also clone this repository and type `make`.  The build requirements
are listed at the end of the [Makefile](Makefile)

#### Syntax highlight in vim

We recommend to add the following lines to `~/.vimrc`

```vim
"elpi
autocmd BufRead,BufNewFile *.elpi set filetype=lprolog

autocmd FileType lprolog syn match   lprologIdentifier  "\<\l[-a-zA-Z\.+*/\\^<>=`'~?@#$&!_]*\>"
autocmd FileType lprolog syn region  lprologClause start="^\<\l[-a-zA-Z\.+*/\\^<>=`'~?@#$&!_]*\>" end=" \|:-\|\."
autocmd FileType lprolog syn match lprologClauseSymbols ":-"
autocmd FileType lprolog syn match lprologClauseSymbols "\."
autocmd FileType lprolog hi def link lprologClauseSymbols Type

autocmd FileType lprolog syn keyword elpiKeyword mode macro type pred namespace rule constraint uvar
autocmd FileType lprolog syn match elpiKeyword ":before"
autocmd FileType lprolog syn match elpiKeyword ":after"
autocmd FileType lprolog syn match elpiKeyword ":name"
autocmd FileType lprolog syn match elpiMacro "@\(\w\|-\)\+"
autocmd FileType lprolog syn match elpiSpill "{"
autocmd FileType lprolog syn match elpiSpill "}"
autocmd FileType lprolog syn region elpiQuotation start="{{" end="}}" contains=@elpiAntiQuotation
autocmd FileType lprolog hi def link elpiKeyword Keyword
autocmd FileType lprolog hi def link elpiMacro Special
autocmd FileType lprolog hi def link elpiSpill Special
```

#### Syntax highlight in $EDITOR

We are happy to merge PRs! (Really, we use vim but we are happy to support
any other editor).

## What's an elaborator and what's so special about it?

The elaborator of an interactive prover is the component in
charge of turning a term as input by the user into a well
typed one.  In a prover like Coq it performs type inference
and is typically extended by the user.

The elaborator manipulates terms with binders and holes 
(unification variables) representing missing piece of 
information.  Some of them have to be filled in in order 
to make the term well typed. Some other are are filled in because 
the user has programmed the eleborator to do so, e.g. ad-hoc polymorphism.

Such software component is characterized by an high complexity
coming from the interplay of binders, reduction and unification,
the heuristics to make it work in practice and the user extensions
to customize its behavior.

## What problem does ELPI (try to) solve and how?

The programming language has the following features
- Native support for variable binding and substitution, via 
  HOAS embedding of the object language.  The programmer needs
  not to care about *De Bruijn indexes*.
- Native support for hypothetical context.  When moving under a
  binder one can attach to the bound variable extra information
  that is collected when the variable gets out of scope.
  For example when writing a type-checker the programmer needs 
  not to care about managing the *typing context*.
- Native support for higher order unification variables, again via HOAS.
  Unification variables of the meta-language (λProlog) can be reused to
  represent the unification variables of the object language.
  The programmer does not need to care about the unification-variable
  *assignment map* and cannot assign to a unification variable a term
  containing variables out of scope, or build a circular assignment. 
- Native support for syntactic constraints and their meta-level handling rules.
  The generative semantics of Prolog can be disabled by turning a goal
  into a constraint (suspended goal). A constraint is resumed as soon as
  relevant variables gets assigned. Suspended constraints can be manipulated
  by constraint handling rules (CHR). Moreover external constraint solvers
  can be integrated to support non syntactic constraints.
  The programmer can declare any set of *constraints that is automatically
  checked for satisfiability* whenever such set gets updates.
- Clauses are graftable. The user is free to *extend an existing program* by
  inserting/removing clauses, both at runtime (using implication) and at
  "parse time" by accumulating files.
- Native support for backtracking. To ease implementation of *search*.

Most of these feature come with λProlog.  Constraints and propagation rules are novel in ELPI.

## Documentation

The language is quite compatible with standard
[λProlog](http://www.lix.polytechnique.fr/~dale/lProlog/) 
and ELPI is known to be able to run most of the λProlog programs out there
(see [INCOMPATIBILITIES](INCOMPATIBILITIES.md) for the known
incompatibilities with the Teyjus system).
Reading "Programming with Higher-Order Logic" by Miller and Nadathur is
highly recommended and covers standard λProlog.

The extensions to λProlog implemented in ELPI are described in the
[ELPI](ELPI.md) file, built-in predicates are documented in
[builtin](builtin.elpi).

There is also a [paper](https://hal.inria.fr/hal-01176856/) describing
the implementation of the interpreter, in particular how it deals with
binder mobility.

#### How to embed ELPI in your software

The easiest way of embedding ELPI is by linking it using
[findlib](http://projects.camlcity.org/projects/findlib.html)
as in `ocamlfind opt -package elpi mycode.ml -o myprogram`.
The API the host application can use to drive ELPI is documented in the
[elpi_API.mli](src/elpi_API.mli) file. The 
[elpi_builtin.ml](src/elpi_builtin.ml) file contains example of
(basic) built-in predicates declaration via ELPI's FFI.

The [command line](elpi_REPL.ml) interface to ELPI is a very simple
example of a client using ELPI as a library.
More complex examples of embeddings of ELPI are
[coq-elpi](https://github.com/LPCIC/coq-elpi) and
[matita-elpi](https://github.com/LPCIC/matita).


