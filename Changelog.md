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
