[![Build Status](https://travis-ci.org/LPCIC/elpi.svg?branch=master)](https://travis-ci.org/LPCIC/elpi)
# ELPI

ELPI implements a variant of λProlog enriched with Constraint Handling Rules.

ELPI is a research project aimed at providing a programming platform
for the so called *elaborator* component of an interactive theorem prover.
ELPI stands for Embeddable Lambda Prolog Interpreter, and indeed it is
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
  The programmer needs not to care about *typing context*.
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
  inserting/removign clauses, both at runtime (using implication) and at
  "parse time" by accumulating files.
- Native support for backtracking. To ease implementation of *search*.

Most of these feature come with λProlog.  Constraints and propagation rules are novel in ELPI.
