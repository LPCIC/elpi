####################
Determinacy checking
####################

A **functional** predicate — declared with ``func``, or ``:functional`` on a
``pred`` (:doc:`../syntax/type-declarations`) — is one the checker can prove
leaves no choice point: every call has at most one solution. Its type is
``(func)`` where a relation's is ``(pred)``. This chapter is what the checker
does with that promise. It is a static, best-effort analysis: not every
non-deterministic call is caught, as the example below shows. See
:ref:`Fissore & Tassi, PADL 2026 <bib-padl2026>` for the full formal
treatment; ``elpi -no-det`` turns the analysis off.


What a functional signature promises
======================================

``map`` is the running example (:ref:`Fissore & Tassi, PADL 2026
<bib-padl2026>` opens with it). Its *basic* signature says only that ``map``
relates a higher-order argument and two lists:

.. code-block:: elpi

   pred map (pred A -> B), list A -> list B.       % basic
   func map (func A -> B), list A -> list B.        % better (this checker)
   map _ [] [].
   map F [X|XS] [Y|YS] :- F X Y, map F XS YS.

The *better* signature says more: **if the higher-order argument ``F`` is a
function, then ``map F`` is a function too** — a call ``map F L R`` with a
functional ``F`` produces a single ``R``. That is the whole content of
writing ``func`` here: a promise about ``map``'s determinacy *conditional on*
its argument's.


Wrongly called predicates
============================

A predicate is **wrongly called** when an argument passed to it is weaker
than its signature asks for — the usual case being a relation passed where a
function was expected. Three one-line definitions of a ``meal`` predicate,
building a list of dishes for a list of guests, show what the checker does
with that (``likes`` is relational — a guest may like several dishes;
``likes!`` is ``likes`` with a trailing cut, so functional):

.. code-block:: elpi

   func meal list guest -> list dish.
   meal Gs Ds :- map likes! Gs Ds.        % accepted: likes! is a function
   meal Gs Ds :- map likes  Gs Ds, !.     % accepted: the cut makes the body one
   meal Gs Ds :- map likes  Gs Ds.        % rejected

The first is fine: ``likes!`` is a function, so ``map likes!`` is, so
``meal``'s body is. The second wrongly calls ``map`` — ``likes`` is only a
relation — but then commits with ``!``, which is enough. The third gets no
such compensation, and the checker rejects it:

.. code-block:: text

   DetCheck: Found relational atom (likes) in the body of function meal.
   Offending term: (likes)
    - Inferred: (Exp [] i-> (Exp [] o-> Rel))
    - Expected: (Exp [] i-> (Exp [] o-> Det))
   Contained in: (map likes Gs Ds)
    - Inferred: Rel
    - Expected: Det

``Rel`` and ``Det`` are how the checker writes ``(pred)`` and ``(func)`` in
its own messages.

Nothing forces the fix to be a cut in ``meal``'s own body. A wrapper whose
signature says "the argument may be any predicate, but the result is a
function" packages the commit safely:

.. code-block:: elpi

   func once (pred A -> B), A -> B.
   once P X R :- P X R, !.
   meal Gs Ds :- map (once likes) Gs Ds.     % accepted

The signature is the interesting part: ``once``'s input is a plain ``pred``,
so passing ``likes`` is *not* a wrong call, yet ``once likes`` is a ``func``.
(This overloads the standard library's ``once``, which wraps a whole goal
rather than a predicate and its arguments.)

A ``pred`` body is not checked, so a *relational* ``meal`` may call
``map likes`` freely — the call runs, it just quietly leaves a choice point
(see the Example). This is how a codebase adopts determinacy checking
incrementally: leave the relations alone, mark ``func`` only what is ready.


Signatures as a subtyping relation
=====================================

A functional signature is *stronger* than a relational one: whatever a
``func`` can do, a ``pred`` can do too, but not the other way round. The
checker compares signatures with a subtyping relation ⊆, read "is at least as
strong as", contravariant on inputs and covariant on outputs: a function
expecting a weaker (more relational) predicate as an input argument accepts a
stronger (more functional) one in its place, and a function promising a
stronger output may be used wherever a weaker one is expected. ``map``'s
better signature is exactly the ⊆-smallest one above the basic one that still
carries the conditional-determinacy promise.


Functional status of outputs
===============================

A signature's *output* being functional is itself information a caller can
use. ``make-deterministic`` turns a two-argument relation into a one-argument
function by picking its first solution and cutting:

.. code-block:: elpi

   func make-deterministic (pred A -> B) -> (func A -> B).
   make-deterministic P (x\y\ P x y, !).

``make-deterministic likes F`` gives an ``F`` the checker can treat as a
``func A -> B`` from then on — for instance, as the argument to ``map``,
now correctly called.


Example
=======

.. elpi:: ../code/wrongly-called.elpi
   :assert: meal: \[pizza, gelato\]\nwrong-meal: \[pizza, gelato\]\nwrong-meal: \[pasta, gelato\]
