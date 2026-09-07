########
Spilling
########

``{ E }`` (:doc:`../syntax/terms-and-operators`) lifts the goal ``E`` out to
just before the smallest enclosing predicate call, replacing ``{ E }`` with a
fresh variable for each argument ``E`` is not given — its output arguments,
so exactly one in the common case:

.. code-block:: elpi

   f X R :- foo X Y, bar Y R.      % written out
   f X R :- bar {foo X} R.         % the same, spilled

If ``E`` has several missing arguments, ``{ E }`` becomes that many variables
at once:

.. code-block:: elpi

   g X R :- h X Y Z, k Y Z R.      % h has two outputs
   g X R :- k {h X} R.             % {h X} stands for the two of them, Y and Z

For this to work Elpi has to know the spilled predicate's arity — from its
``pred`` / ``func`` signature (:doc:`../syntax/type-declarations`); an
undeclared predicate cannot be spilled.

The spilled call is inserted just before the *closest* call recognised as a
predicate — today that means a monomorphic, first-order signature; a
polymorphic or higher-order argument position (as in an anonymous predicate
passed to ``std.map``) may place it one level up if the callee's own type
isn't precise enough to pin it down. ``elpi -print FILE`` prints a program
after spilling (and other compilation passes), so any doubt about where a
particular ``{ }`` ended up can be checked directly.


Spilling into a binder
========================

Under ``pi``, under a bare lambda, and under ``==>``, the spilled goal is
placed *inside* the binder, so its fresh variable can still mention whatever
names and hypotheses are in scope there. A pretty-printer that recurses under
``lam`` spills ``{pp (F x)}`` right where the fresh ``x`` and its
``pp x "x"`` hypothesis are visible:

.. elpi:: ../code/spilling-under-binder.elpi
   :assert: \\x.\(x x\)

``elpi -print FILE`` shows where the spilled goal landed: in the ``lam`` rule
it sits after the ``==>``, inside the ``pi`` and under its own ``sigma``,
equivalent to writing

.. code-block:: elpi

   pp (lam F) S :- pi x\ pp x "x" ==> sigma R\ (pp (F x) R, S is "\x." ^ R).


When ``{ }`` wraps a conjunction, only its *last* conjunct is spilled — that
conjunct's missing output is what becomes the fresh variable. The earlier
conjuncts run in place, typically to bind a variable the last one then reads:

.. code-block:: elpi

   foo :- pi x\ f {g x Y, h Y}.
   % becomes
   foo :- pi x\ sigma S\ (g x Y, h Y S), f S.

``g x Y`` runs first and binds ``Y``; ``h Y`` is the spilled conjunct, so
``h Y S`` computes the value ``S`` that takes the place of the whole
``{ … }``.

Example
=======

Spilling lets a "function-like" predicate call appear where a term is expected:
the expression between ``{`` and ``}`` is lifted out and run just before the
enclosing call. Here ``{std.rev L}`` becomes a fresh variable produced by an
``std.rev`` goal inserted right before ``std.append``:

.. elpi:: ../code/palindrome.elpi
   :assert: \[1, 2, 3, 3, 2, 1\]
