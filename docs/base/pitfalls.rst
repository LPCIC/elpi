########
Pitfalls
########

A collection of mistakes that trip up newcomers and veterans alike, each
cross-referencing where it is covered in depth.


Misleading precedence of ``,``, ``=>`` and ``==>``
======================================================

``=>`` binds *tighter* than ``,``: ``A, B => C, D`` means ``A, (B => C), D`` —
the hypothesis ``B`` is available only to ``C``, not to the rest of the
conjunction. This is a common mistake, since a newcomer typically expects
``B`` to hold for everything that follows. Adding a debug print between ``C``
and ``D``, as in ``A, B => print C, D``, shows exactly where the hypothesis
ends: ``print C`` still sees ``B``, but ``D`` runs *outside* it. ``==>`` was
introduced with the opposite precedence specifically to avoid this —
``A, B ==> C, D`` reads ``A, (B ==> (C, D))``, so the hypothesis reaches
everything after it — and Elpi warns on the traditional ``=>`` spelling; see
:doc:`syntax/inference-rules-and-queries`.


Treacherous one-rule anonymous predicates
============================================

A variable is a parameter of the *whole rule* it occurs in, not of an
anonymous predicate nested inside it — so a variable used only inside a
``std.map`` (or similar) callback is shared by every call the traversal
makes, not fresh per call, unless a ``sigma`` says otherwise
(:doc:`features/binders-and-hoas`):

.. elpi:: code/anonymous-predicate.elpi
   :assert: wrong: fails \(A can't be both 2 and 3\)\nright: \[20, 30, 40\]

A named, top-level predicate sidesteps the issue entirely — its own variables
are fresh at every call by construction, with no ``sigma`` to remember.


Scope error as a silent failure
==================================

A unification that fails because a term escapes its scope (a hole assigned a
value that mentions a name it cannot see) just fails, with nothing marking it
as different from an ordinary logical failure. In practice this is almost
always a mistake, not a deliberate use of scoping — most often, a variable
used right after a ``pi``/``sigma`` that needed its own, inner ``sigma``
(:doc:`features/binders-and-hoas`) rather than reusing one from further out.
If a goal fails for no apparent reason, a scope mismatch is worth checking
before anything else.


``=!=>`` and functional predicates
=====================================

Adding a rule to a ``func`` predicate at run time, through ``==>``, can trip
the determinacy checker even when the rule is only ever meant to fire once —
``=!=>`` adds the missing cut automatically; see
:doc:`features/hypothetical-rules`.


Taming backtracking
======================

``std.do! [G1, G2, …]`` runs a sequence of goals as if cut followed each one,
closer to imperative sequencing than a bare conjunction; ``std.spy``/``std.spy!``
print a goal's calls without needing any command-line flag. See
:doc:`features/control-and-cut` and :doc:`debugging-and-tracing`.


Unification variables are not imperative variables
=======================================================

``X = 1`` does not *set* ``X`` — it unifies it, once, for good (until
backtracking undoes it). A later ``X = 2`` does not overwrite it: it tries to
unify the already-1 ``X`` with ``2``, and fails, since ``1`` and ``2`` are not
the same term:

.. elpi:: code/logic-variable.elpi
   :assert: X is now 1\ncannot reassign: X is already 1, not 2

Code that needs an evolving value across a computation should thread a fresh
variable through each step (:doc:`features/binders-and-hoas` — ``sigma`` for
each new one) or use the constraint store as an explicit global
(:doc:`semantics/chr`), not repeated assignment to the same variable.


Symmetric CHR rules and the multiset store
==============================================

A constraint handling rule with two patterns and no ``\`` can fire once per
*ordering* of two matching constraints, since the store is a multiset — a
surprise the first time it is seen. See :doc:`semantics/chr`.
