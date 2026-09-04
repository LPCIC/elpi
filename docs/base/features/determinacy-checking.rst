####################
Determinacy checking
####################

A **functional** predicate — declared with ``func``, or ``:functional`` on a
``pred`` (:doc:`../syntax/type-declarations`) — is one the checker can prove
leaves no choice point: every call has at most one solution. Internally its
type is tagged ``fprop`` rather than ``prop`` — it may show up that way in an
error message. This chapter is what the checker does with that promise. It is
a static, best-effort analysis: not every non-deterministic call is caught,
as the example below shows. See :ref:`Fissore & Tassi, PADL 2026 <bib-padl2026>`
for the full formal treatment; ``elpi -no-det`` turns the analysis off.


Signatures as a subtyping relation
=====================================

A functional signature is *stronger* than a relational one: whatever a
``func`` can do, a ``pred`` can do too, but not the other way round. The
checker compares signatures with a subtyping relation ⊆, read "is at least as
strong as", contravariant on inputs and covariant on outputs: a function
expecting a weaker (more relational) predicate as an input argument accepts a
stronger (more functional) one in its place, and a function promising a
stronger output may be used wherever a weaker one is expected.


Wrongly called predicates
============================

A predicate is **wrongly called** when an argument passed to it is weaker
than its signature expects — most often, a relational predicate passed where
a functional one was promised. This does not stop the call: it just breaks
the functional guarantee for that one call, possibly silently (see the
Example below). Both calls to ``map`` there type-check and run; only the one
passed the relational
``likes`` actually leaves a choice point, silently — nothing marks the second
``map`` call as suspect ahead of time. This is also how a codebase adopts
determinacy checking incrementally: keep ``likes`` as it is and add a
``likes!`` wrapper (``likes! A B :- likes A B, !.``) for the call sites that
are known to need a single answer, rather than rewriting everything at once.


Functional status of outputs
===============================

A signature's *output* being functional is itself information a caller can
use. ``make-deterministic`` turns a two-argument relation into a one-argument
function by picking its first solution and cutting:

.. code-block:: elpi

   func make-deterministic (pred i:A, o:B) -> (func A -> B).
   make-deterministic P (x\y\ P x y, !).

``make-deterministic likes F`` gives an ``F`` the checker can treat as a
``func A -> B`` from then on — for instance, as the argument to ``map`` above,
now correctly called.


Example
=======

.. elpi:: ../code/wrongly-called.elpi
   :assert: correctly called: \[pizza, gelato\]\nwrongly called: \[pizza, gelato\]\nwrongly called: \[pasta, gelato\]\nwrongly called: backtracked into a second result
