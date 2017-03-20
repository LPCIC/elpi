[![Build Status](https://travis-ci.org/LPCIC/elpi.svg?branch=master)](https://travis-ci.org/LPCIC/elpi)
# ELPI

ELPI implements a variant of λProlog enriched with Constraint Handling Rules.

ELPI is a research project aimed at providing a programming platform
for the so called *elaborator* component of an interactive theorem prover.
ELPI strands for Embeddable Lambda Prolog Interpreter, and indeed it is
designed to be easily embedded into larger softwares written in OCaml
as Coq or Matita.

ELPI is free software released under LGPL vesion 2.1 or above.

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

Such software component typically encompasses heuristics,
extension languages, an more in general an high complexity deriving
from the interplay of binders, reduction and unification.

## What problem does ELPI (try to) solve and how?

The programming language has the following features
- Native support for variable binding and substitution, via HOAS embedding of the object language.  The programmer needs not to care about *De Bruijn indexes*.
- Native support for hypothetical context.  When moving under a binder one can attach to the bound variable extra information that is collected when the variable gets out of scope.   The programmer needs not to care about *typing context*.
- Native support for unification variables, again via HOAS, constraints and their meta-level handling rules.  Unification variables of the meta-language (λProlog) can be reused to represent the unification variables of the object language.  The generative semantics of Prolog can be disabled by turning a goal into a constrain and constraints can be combined by constraint handling rules.  The programmer needs not to care about *unification variable* substitution or occur-check.
- Graftable clauses.  The user is free to *extend* a program by inserting/removign clauses.
- Native support for Backtracking. To ease implementation of *search*.

Most of these feature come with λProlog.  Constraints and propagation rules are novel in ELPI.
