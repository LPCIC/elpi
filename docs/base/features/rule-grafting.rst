#############
Rule grafting
#############

The attribute syntax — ``:name``, ``:before``, ``:after``, ``:replace``,
``:remove`` — is :doc:`../syntax/file-structure-and-attributes`. This chapter
is what grafting is *for*, and its restrictions.


Overriding library behaviour
==============================

A library gives a rule a stable name so that code accumulated later can
change what happens without touching the library file itself — a common
pattern for a "fatal error" or "default handler" rule a client wants to
customize — see the Example below. Once ``custom-report`` cuts,
``default-report`` is never tried for this call;
without the cut, both would run on backtracking. ``:after`` inserts the other
way around — after the named rule instead of before it.


Restrictions
==============

``:replace`` and ``:remove`` only ever act on a rule of the *same* predicate
— attaching one to a rule that names another predicate's rule is a hard
error ("cannot remove a clause for another predicate"), which keeps a typo in
the name string from silently doing nothing. The replacing (or removed) rule
also cannot itself carry ``:name``: allowing it would make the outcome depend
on the order two files that both replace the same rule are accumulated in,
which :doc:`../syntax/file-structure-and-attributes` deliberately rules out.


Example
=======

.. elpi:: ../code/grafting.elpi
   :assert: custom: hello
