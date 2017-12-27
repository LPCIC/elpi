
## Version 1 (Jan 2018?)
Second public release, developed in tandem with coq-elpi and matita-elpi.

The programming language features constraints (suspended goals) and
a meta language (inspired by CHR) to manipulate the constrain store.

There is an API for clients letting one drive the interpreter and
extend the set of built-in predicates, register quotations and
antiquotations, etc.

The software is now built using findlib into a library.
The standalone interpreter is just a regular client of the API.

All language features are documented in the [ELPI.md](ELPI.md) file.
The client API is documented in [elpi_API.mli](src/elpi_API.mli).

## LPAR 2015 (Jul 12, 2015)
First public release accompaining the paper 
[ELPI: fast, Embeddable, λProlog Interpreter](https://hal.inria.fr/hal-01176856/)
