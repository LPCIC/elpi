########
Spilling
########

.. note::

   **Stub — part of the manual outline.**

   Planned content: How ``{ }`` is rewritten; the spilled predicate's arity must be known (from its signature); spilling under ``pi``, under a lambda, under implication and under conjunction; the caveats; ``-print``.

   Source material: ELPI.md “Spilling”; HDR §2.6.2; coq-elpi tutorial “Spilling (relation composition)”.

Example
=======

Spilling lets a "function-like" predicate call appear where a term is expected:
the expression between ``{`` and ``}`` is lifted out and run just before the
enclosing call. Here ``{std.rev L}`` becomes a fresh variable produced by an
``std.rev`` goal inserted right before ``std.append``:

.. elpi:: ../code/palindrome.elpi
   :assert: \[1, 2, 3, 3, 2, 1\]
