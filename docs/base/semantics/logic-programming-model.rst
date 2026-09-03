###########################
The logic programming model
###########################

.. note::

   **Stub — part of the manual outline.**

   Planned content: Elpi vs. Prolog: algebraic data types, rules (head and premises), unification of the head with the goal (non-linear heads are fine), backtracking search, the hard cut ``!``. Elpi vs. λProlog: HOAS / λ-tree syntax, bound vs. unification variables, unification variables with a scope, ``pi`` (fresh names), ``=>`` (dynamic / hypothetical rules), the context Γ, Hereditary Harrop formulas, and the divergence problem that motivates constraints. The Lλ and Lβλ fragments.

   Source material: HDR §2.1-2.2; coq-elpi tutorial (Logic programming … Logical foundations).

Example
=======

A program is a set of rules; a rule fires when its head unifies with the goal,
producing the premises as new goals; the search backtracks over the rules.

.. elpi:: ../code/family.elpi
   :assert: bob is older than alice
