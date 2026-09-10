########
Spilling
########

A rule that threads a value from one call straight into the next has to name
that value, and a name like ``Tmp`` or ``Aux1`` carries no information: it is
there only to plumb the two calls together. Spilling removes the name. ``{ E }``
(:doc:`../syntax/terms`) lifts the goal ``E`` out to just before the smallest
enclosing predicate call and puts a fresh variable in its place, one for each
argument ``E`` is not given (its output arguments, so one in the common
case):

.. code-block:: elpi

   f X R :- foo X Y, bar Y R.      % written out, with the plumbing variable Y
   f X R :- bar {foo X} R.         % the same, spilled

If ``E`` has several missing arguments, ``{ E }`` becomes that many variables
at once:

.. code-block:: elpi

   g X R :- h X Y Z, k Y Z R.      % h has two outputs
   g X R :- k {h X} R.             % {h X} stands for the two of them, Y and Z

For this to work Elpi has to know the spilled predicate's arity, from its
``pred`` / ``func`` signature (:doc:`../syntax/type-declarations`); an
undeclared predicate cannot be spilled.

The spilled call is inserted just before the *closest* call recognised as a
predicate, which today means a monomorphic, first-order signature; a
polymorphic or higher-order argument position (as in an anonymous predicate
passed to ``std.map``) may place it one level up if the callee's own type
isn't precise enough to pin it down. ``elpi -print FILE`` prints a program
after spilling (and other compilation passes), so any doubt about where a
particular ``{ }`` ended up can be checked directly.

Here ``{std.rev L}`` becomes a fresh variable produced by an ``std.rev`` goal
inserted right before ``std.append``:

.. elpi:: ../code/palindrome.elpi
   :assert: \[1, 2, 3, 3, 2, 1\]


Spilling into a binder
======================

Under ``pi`` and in the conclusion of ``==>``, the spilled goal is placed
*inside* the binder, so its fresh variable can still mention the names and
hypotheses in scope there. A pretty-printer that recurses under ``lam`` spills
``{pp (F x)}`` right where the fresh ``x`` and its ``pp x "x"`` hypothesis are
visible:

.. elpi:: ../code/spilling-under-binder.elpi
   :assert: \\x.\(x x\)

``elpi -print FILE`` shows where the spilled goal landed: in the ``lam`` rule
it sits after the ``==>``, inside the ``pi`` and under its own ``sigma``,
equivalent to writing

.. code-block:: elpi

   pp (lam F) S :- pi x\ pp x "x" ==> sigma R\ (pp (F x) R, S is "\x." ^ R).

Only the *conclusion* of an implication may spill. A ``{ }`` in the
hypothesis is rejected at compile time (``Spilling in negative position is
forbidden``), since the lifted goal would have to run before the hypothesis
it depends on is in scope.


Spilling out of a term-level lambda
===================================

A ``{ }`` inside a lambda that is passed as *data*, not the body of a ``pi``
or an implication, goes the other way: the goal is lifted *out* past the
lambda and the fresh variable is η-expanded so it can still depend on the
bound name. ``apply (x\ {f x})`` becomes

.. code-block:: elpi

   main :- apply (x\ {f x}).
   % becomes
   main :- pi c\ f c (R c), apply (x\ R x).

The spilled ``f c`` runs once, before ``apply``, with ``c`` a fresh constant.
This is only meaningful when ``f`` does not actually need ``c``'s value; a
``{ }`` under a term-level lambda that genuinely depends on the bound variable
is usually a mistake.


Spilling a conjunction
======================

When ``{ }`` wraps a conjunction, only its *last* conjunct is spilled, and
that conjunct's missing output is what becomes the fresh variable. The earlier
conjuncts run in place, typically to bind a variable the last one then reads:

.. code-block:: elpi

   foo :- pi x\ f {g x Y, h Y}.
   % becomes
   foo :- pi x\ sigma S\ (g x Y, h Y S), f S.

``g x Y`` runs first and binds ``Y``; ``h Y`` is the spilled conjunct, so
``h Y S`` computes the value ``S`` that takes the place of the whole
``{ … }``.
