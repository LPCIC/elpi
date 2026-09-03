####################
Determinacy checking
####################

A **functional** predicate, one declared with ``func``
(:doc:`../syntax/type-declarations`), is one the checker can prove leaves no
choice point: every call has at most one solution. Its type is
``(func)`` where a relation's is ``(pred)``. What the checker does with that
promise is a static, best-effort analysis: not every non-deterministic call
is caught. See
:ref:`Fissore & Tassi, PADL 2026 <bib-padl2026>` for the full formal
treatment; ``elpi -no-det`` turns the analysis off.

The check is worth having because the code it applies to is overwhelmingly
functional: :ref:`the HDR thesis <bib-hdr>` measures around 96% of the
predicates in Elpi's own code and in coq-elpi as computing a function rather
than a relation. A left-over choice point in one of them is almost always a
bug, and one that surfaces far from its cause.


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
function, then ``map F`` is a function too**: a call ``map F L R`` with a
functional ``F`` produces a single ``R``. That is the whole content of
writing ``func`` here: a promise about ``map``'s determinacy *conditional on*
its argument's.


What the checker requires
=========================

For a ``func`` to be accepted, three things must hold, and each has its own
error message so a rejection says which one failed:

* **its rules are mutually exclusive**: no two can fire for the same call
  without one of them cutting. Two overlapping heads with no cut give
  ``Mutual exclusion violated for rules of predicate …``.
* **every atom in its body is itself functional**: a relational call in a
  ``func`` body is ``Found relational atom (…) in the body of function …``,
  unless a ``!`` after it collapses the choice point.
* **its outputs come back as single values**: an output argument left as a
  relation, rather than pinned to one term, is rejected where the ``func``
  signature promised a function.

The checker does not run the body; it reasons from the signatures. A call it
cannot prove functional it rejects, even when the program would in fact be
deterministic. ``elpi -no-det``, or a wider ``pred`` signature, is the way
out when that happens.


Wrongly called predicates
============================

A predicate is **wrongly called** when an argument passed to it is weaker
than its signature asks for, the usual case being a relation passed where a
function was expected. Three one-line definitions of a ``meal`` predicate,
building a list of dishes for a list of guests, show what the checker does
with that (``likes`` is relational, since a guest may like several dishes;
``likes!`` is ``likes`` with a trailing cut, so functional):

.. code-block:: elpi

   func meal list guest -> list dish.
   meal Gs Ds :- map likes! Gs Ds.        % accepted: likes! is a function
   meal Gs Ds :- map likes  Gs Ds, !.     % accepted: the cut makes the body one
   meal Gs Ds :- map likes  Gs Ds.        % rejected

The first is fine: ``likes!`` is a function, so ``map likes!`` is, so
``meal``'s body is. The second wrongly calls ``map``, since ``likes`` is only
a relation, but then commits with ``!``, which is enough. The third gets no
such compensation, and the checker rejects it:

.. code-block:: text

   DetCheck: Found relational atom (likes) in the body of function meal.
   Offending term: (likes)
    - Inferred: (pred any -> any)
    - Expected: (func any -> any)
   Contained in: (map likes Gs Ds)
    - Inferred: (pred)
    - Expected: (func)

Nothing forces the fix to be a cut in ``meal``'s own body. A wrapper whose
signature says "the argument may be any predicate, but the result is a
function" packages the commit safely:

.. code-block:: elpi

   func commit (pred A -> B), A -> B.
   commit P X R :- P X R, !.
   meal Gs Ds :- map (commit likes) Gs Ds.     % accepted

The signature is the interesting part: ``commit``'s input is a plain
``pred``, so passing ``likes`` is *not* a wrong call, yet ``commit likes`` is
a ``func``. PADL calls this combinator ``once``; it is a two-argument
analogue of the standard library's ``std.once``, which commits a whole goal
rather than a predicate applied to its arguments.

The body of a ``pred`` is still traversed, but the comparison that would
reject a relational atom in it is vacuous (a ``pred`` body is allowed to be
relational), so a *relational* ``meal`` may call ``map likes`` freely: the
call runs, it just quietly leaves a choice point. The output signatures of a
``pred`` are checked all the same. This is how a codebase adopts determinacy
checking incrementally: leave the relations alone, mark ``func`` only what is
ready.

.. elpi:: ../code/wrongly-called.elpi
   :assert: meal: \[pizza, gelato\]\nwrong-meal: \[pizza, gelato\]\nwrong-meal: \[pasta, gelato\]

``meal`` is a ``func`` and passes ``likes!``; ``wrong-meal`` is a ``pred`` and
gets away with the plain relation ``likes``, whose extra solutions
backtracking then walks into.


A function that extends the program
===================================

A ``func`` may add rules to itself at run time and stay a ``func``. The
standard shape is a HOAS traversal that goes under a binder: ``copy`` copies a
term, and under ``lam`` it needs a ``copy x x`` rule for the fresh bound
variable. Added with plain ``==>`` that rule overlaps the structural ones and
mutual exclusion fails; added with ``=!=>``
(:doc:`../syntax/inference-rules-and-queries`) it carries a cut at the end of
its body, so the checker still sees a single-valued ``copy``:

.. elpi:: ../code/functional-hoas.elpi
   :assert: copied: lam c\d+ \\ app c\d+ c\d+

This is what ``=!=>`` is *for*: a rule known only at run time, meant to fire
once, in a predicate the checker must keep treating as deterministic.


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
use. For instance ``func id A -> A`` (with the single rule ``id X X``)
promises whoever receives its output a value, not a choice among values.

That guarantee cannot be conjured from a relation for free. ``make-deterministic``
(PADL's ``commit``) manufactures it, turning a two-argument relation into a
one-argument function by picking the first solution and cutting:

.. code-block:: elpi

   func make-deterministic (pred A -> B) -> (func A -> B).
   make-deterministic P (x\y\ P x y, !).

``make-deterministic likes F`` gives an ``F`` the checker can treat as a
``func A -> B`` from then on, for instance as the argument to ``map``,
now correctly called. Passing ``likes`` itself in that position, with no
``make-deterministic`` around it, is the wrong call of the previous section.
