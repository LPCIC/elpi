################
Binders and HOAS
################

:doc:`../semantics/logic-programming-model` introduces ``x\ t`` and ``pi`` for
encoding object-language binders (:doc:`../syntax/terms-and-operators`,
:doc:`../syntax/inference-rules-and-queries`). This chapter is the practical
side: writing code that goes under a binder, and inspecting what is currently
in scope.


``sigma`` for per-call locals
==============================

``sigma X\ g`` allocates a fresh unification variable for the duration of
``g``. It matters most in an otherwise variable-free, one-rule predicate: a
top-level variable is shared by every call to a predicate that has only one
rule (:doc:`../syntax/inference-rules-and-queries`), so a rule like
``fresh-pair (pr X Y) :- sigma X\ sigma Y\ true.`` needs the explicit
``sigma`` to get a *new* ``X``/``Y`` each time it runs, rather than reusing
whatever the first call happened to assign.

Any variable used for the first time *after* a ``pi``/``sigma`` still needs
its own ``sigma`` to be usable there — a variable's scope is fixed by where it
is introduced, not by where it is later mentioned. ``main :- pi x\ (names Ns,
…)`` fails silently: ``Ns`` belongs to ``main``'s own outermost scope, which
cannot see ``x``, so assigning it the list ``[x]`` is a scope error. Writing
``main :- pi x\ sigma Ns\ (names Ns, …)`` fixes it.


Moving under a binder
=======================

Recursing into a ``lam`` argument follows the same shape as the STLC type
checker's abstraction rule: introduce a fresh name with ``pi``, recurse on the
function applied to it. A predicate computing the nesting depth of a term:

.. code-block:: elpi

   pred depth i:tm, o:int.
   depth (app H A) N :- !, depth H N1, depth A N2, N is {std.max N1 N2}.
   depth (lam F) N :- !, pi x\ depth (F x) N1, N is N1 + 1.
   depth _ 0.

goes one level deeper each time it opens a ``lam``, and the fresh ``x`` is
simply discarded — the recursive call only needs it to instantiate ``F``, not
to inspect it.


Inspecting the context
========================

Three builtins introspect the eigenvariables — the eigen names ``pi`` has
introduced so far — a call is running under:

* ``names L`` lists them, youngest first;
* ``occurs N T`` checks whether the name (or global constant) ``N`` appears in
  ``T``;
* ``closed_term T`` unifies ``T`` with a fresh variable that cannot see *any*
  of them — a way to produce a value that must not depend on the current
  binders, and get a clear failure if it accidentally does.


Example
=======

.. elpi:: ../code/binders.elpi
   :assert: depth: 2\neigenvariables in scope: 2\nx occurs in \(app x y\): yes\nclosed_term succeeded
