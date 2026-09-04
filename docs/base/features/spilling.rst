########
Spilling
########

``{ E }`` (:doc:`../syntax/terms-and-operators`) lifts the goal ``E`` out to
just before the smallest enclosing predicate call, replacing ``{ E }`` itself
with a fresh variable bound to ``E``'s last argument:

.. code-block:: elpi

   f X R :- foo X Y, bar Y R.      % written out
   f X R :- bar {foo X} R.         % the same, spilled

For this to work Elpi has to know ``foo``'s arity — from its ``pred`` / ``func``
signature (:doc:`../syntax/type-declarations`); an undeclared predicate cannot
be spilled.

Spilling reaches into a binder: under ``pi``, under a bare lambda, and under
``==>``, the inserted goal is placed *inside* the binder, so the fresh
variable still depends on whatever names or hypotheses are in scope there —
spilling a conjunction spills only its last conjunct:

.. code-block:: elpi

   foo :- pi x\ f {g x}.
   % becomes
   foo :- pi x\ sigma S\ g x S, f S.

   foo R :- R = x\ g {h x, mk-app f [x, g x]}.
   % becomes
   foo R :- (pi x\ sigma S\ h x, mk-app f [x, g x] S), R = x\ g S.

The spilled call is inserted just before the *closest* call recognised as a
predicate — today that means a monomorphic, first-order signature; a
polymorphic or higher-order argument position (as in an anonymous predicate
passed to ``std.map``) may place it one level up if the callee's own type
isn't precise enough to pin it down. ``elpi -print FILE`` prints a program
after spilling (and other compilation passes), so any doubt about where a
particular ``{ }`` ended up can be checked directly.


Example
=======

Spilling lets a "function-like" predicate call appear where a term is expected:
the expression between ``{`` and ``}`` is lifted out and run just before the
enclosing call. Here ``{std.rev L}`` becomes a fresh variable produced by an
``std.rev`` goal inserted right before ``std.append``:

.. elpi:: ../code/palindrome.elpi
   :assert: \[1, 2, 3, 3, 2, 1\]
