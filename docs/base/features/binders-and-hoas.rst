################
Binders and HOAS
################

Writing code that goes under a binder, and inspecting what is currently in
scope. The encoding of object-language binders with ``x\ t`` and ``pi`` is
:doc:`../semantics/logic-programming-model` (:doc:`../syntax/terms`,
:doc:`../syntax/inference-rules-and-queries`).


Moving under a binder
=======================

Recursing into a ``lam`` argument follows the same shape as the STLC type
checker's abstraction rule: introduce a fresh name with ``pi``, then recurse
on the function applied to it. A function computing the nesting depth of a
term:

.. code-block:: elpi

   func depth tm -> int.
   depth (app H A) N :- !, depth H N1, depth A N2, N is {std.max N1 N2}.
   depth (lam F) N :- !, pi x\ depth (F x) N1, N is N1 + 1.
   depth X 0 :- name X.

It goes one level deeper each time it opens a ``lam``. The fresh ``x`` is
never inspected, the recursive call only needing it to instantiate ``F``, and
the base rule guards on ``name X``, so it fires for a bound variable but not
for an ``app``, a ``lam``, or an unassigned hole.


``sigma`` for per-call locals
==============================

``sigma X\ g`` allocates a fresh unification variable ``X`` for the duration
of ``g``. An ordinary rule variable does not need it: each use of a rule
already gets its own fresh variables
(:doc:`../syntax/inference-rules-and-queries`). ``sigma`` matters in the two
situations where that is not enough.

The first is a variable used inside an anonymous predicate, the callback
passed to ``std.map`` and the like. Such a variable belongs to the enclosing
rule, not to the callback, so it is the *same* variable on every call the
traversal makes; a ``sigma`` inside the callback gives each call its own.

The second is a variable first used *after* a ``pi`` or ``sigma``. A
variable's scope is fixed where it is introduced, not where it is later
mentioned, so ``main :- pi x\ (names Ns, …)`` fails silently: ``Ns`` belongs
to ``main``'s outer scope, which cannot see ``x``, so assigning it the list
``[x]`` is a scope error. Writing ``main :- pi x\ sigma Ns\ (names Ns, …)``
introduces ``Ns`` in the right place and works.


Inspecting the context
========================

Two builtins introspect the eigenvariables (the names ``pi`` has introduced
so far) that a call is running under:

* ``names L`` lists them, youngest first;
* ``occurs N T`` checks whether the name (or global constant) ``N`` appears in
  ``T``.


Restricting a variable's scope
================================

A fresh unification variable created under ``pi x\ pi y\`` may mention ``x``
and ``y`` in its eventual assignment: its *scope*. Elpi's printer writes that
as ``X0^2``: the variable ``X0``, with two eigenvariables in scope.

``prune V L`` shrinks that: it unifies ``V`` with a *fresh* variable whose
scope is the names in ``L``. It does not edit ``V`` in place; the old
variable and the new, narrower one are simply unified, so any later
assignment has to satisfy both. After ``prune P [x]``, printing ``P`` shows
that fresh variable applied to ``x`` alone (``x`` prints as ``c0``): it may
name ``x`` but not ``y``.

``closed_term T`` is ``prune T []``: a variable that can see *nothing*. It is
the way to produce a value that must not depend on the current binders.

The narrowing is a *unification*, so it can also fail: if ``V`` is already
bound to a term that mentions a name outside ``L`` (outside all names, for
``closed_term``), there is no way to satisfy both scopes and the call fails.
``closed_term (app x y)`` under ``pi x\ pi y\`` fails rather than quietly
forgetting ``x`` and ``y``. On an *unbound* variable it always succeeds; the
failure is the useful signal when the argument is the output of a computation
that was supposed to stay closed.

A scope violation that happens through ordinary unification, rather than
through ``prune`` / ``closed_term``, fails silently instead.

Recursing under a binder, inspecting the eigenvariables in scope, and
narrowing a variable's scope with ``prune`` and ``closed_term``, in one
program:

.. elpi:: ../code/binders.elpi
   :assert: depth: 2\neigenvariables in scope: 2\nx occurs in \(app x y\): yes\nT sees both eigenvariables: X\d+\^2\nP pruned to just x: X\d+ c\d+\nT after closed_term, sees none: X\d+\nclosed_term \(app x y\) fails: it already mentions x and y
