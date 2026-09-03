########
Pitfalls
########

A collection of mistakes that trip up newcomers and veterans alike, each
cross-referencing where it is covered in depth.


Misleading precedence of ``=>``
===============================

If a hypothesis added with ``=>`` does not reach the goals you expect, this is
almost always why: ``=>`` binds tighter than ``,``, so in ``A, B => C, D`` the
hypothesis ``B`` reaches only ``C``, not ``D``. A debug print between the
goals, ``A, B => print C, D``, shows where it stops: ``print C`` sees ``B``,
``D`` does not. The fix is ``==>``, which binds looser than ``,``; Elpi also
warns where the ``=>`` precedence bites. The parse rules are given in
:doc:`../syntax/inference-rules-and-queries`.


Treacherous one-rule anonymous predicates
============================================

A variable is a parameter of the *whole rule* it occurs in, not of an
anonymous predicate nested inside it, so a variable used only inside a
``std.map`` (or similar) callback is shared by every call the traversal
makes, not fresh per call, unless a ``sigma`` says otherwise
(:doc:`binders-and-hoas`):

.. elpi:: ../code/anonymous-predicate.elpi
   :assert: wrong: fails \(A can't be both 2 and 3\)\nright: \[20, 30, 40\]

A named, top-level predicate sidesteps the issue entirely: its own variables
are fresh at every call by construction, with no ``sigma`` to remember.


Scope error as a silent failure
==================================

A unification that fails because a term escapes its scope (a hole assigned a
value that mentions a name it cannot see) fails with nothing marking it as
different from an ordinary logical failure. In practice this is almost always
a mistake, not a deliberate use of scoping: most often, a variable used right
after a ``pi``/``sigma`` that needed its own, inner ``sigma``
(:doc:`binders-and-hoas`) rather than reusing one from further out.
If a goal fails for no apparent reason, a scope mismatch is worth checking
before anything else.


``=!=>`` and functional predicates
=====================================

Adding a rule to a ``func`` predicate at run time, through ``==>``, can trip
the determinacy checker even when the rule is only ever meant to fire once.
``=!=>`` adds the missing cut automatically; see
:doc:`../syntax/inference-rules-and-queries`.


Unification variables are not imperative variables
=======================================================

``X = 1`` does not *set* ``X``; it unifies it, once, for good (until
backtracking undoes it). A later ``X = 2`` does not overwrite it: it tries to
unify the already-1 ``X`` with ``2``, and fails, since ``1`` and ``2`` are not
the same term:

.. elpi:: ../code/logic-variable.elpi
   :assert: X is now 1\ncannot reassign: X is already 1, not 2

Code that needs an evolving value across a computation should thread a fresh
variable through each step (:doc:`binders-and-hoas`, ``sigma`` for each new
one) or use the constraint store as an explicit global
(:doc:`../semantics/chr`), not repeated assignment to the same variable.
