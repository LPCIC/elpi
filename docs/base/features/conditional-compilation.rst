########################
Conditional compilation
########################

``:if`` (:doc:`../syntax/file-structure-and-attributes`) is a rule attribute;
this chapter is what it does and the lexer-level alternative next to it.


``:if`` and ``-D``
=====================

A rule marked ``:if "NAME"`` is part of the program only when the compiler
variable ``NAME`` is defined — otherwise it is dropped as if it had never
been written, with no trace at run time. ``elpi -D NAME`` (repeatable) defines
one; it is just an arbitrary string, not tied to any particular predicate.
The typical use is a debug-only rule, silent by default (see the Example
below) unless ``DEBUG`` is defined:

.. code-block:: console

   $ elpi conditional.elpi -test -D DEBUG
   [debug] checkpoint 1
   done

``:if`` also works on CHR rules (:doc:`../syntax/constraint-handling-rules`).


The lexer directives
======================

``% elpi:if version … / % elpi:endif`` and ``% elpi:skip N``
(:doc:`../syntax/file-structure-and-attributes`) act earlier, before parsing:
they drop *text*, not rules, which is what makes them able to hide syntax
Elpi itself does not accept — a directive meant for Teyjus, say, kept in a
file both interpreters share.


Example
=======

.. elpi:: ../code/conditional.elpi
   :assert: done
