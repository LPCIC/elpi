####################
Organizing a program
####################

``accumulate``, ``namespace``, ``shorten`` and the leading-``.`` escape are
:doc:`../syntax/file-structure-and-attributes`. This chapter is how they
combine into an actual multi-file program.


The search path
=================

``accumulate name.`` first looks for ``name.elpi`` relative to the
accumulating file; if that fails, it looks along every directory passed with
``elpi -I PATH`` (repeatable). This is how a library can be accumulated by
name from a program that does not know where it is installed.


Namespaces nest
=================

``namespace`` blocks nest, and so do their prefixes: a predicate declared
inside ``namespace outer { namespace inner { … } }`` is reached from the
outside as ``outer.inner.name``.


A library's public surface
=============================

Combining namespacing and ``shorten`` is how a file exposes a small public
API while keeping its helpers out of the way: nest the helpers under an
``internal`` namespace, define the public predicates next to it (able to
reach ``internal.…`` without qualification, since they are in the same
enclosing namespace), and ``shorten`` only the public names for whoever
accumulates the file — see the Example below.


Example
=======

.. elpi:: ../code/library-api.elpi
   :assert: result: 21
