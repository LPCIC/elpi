#######################
Types and type checking
#######################

Types have no role at run time (:doc:`../syntax/type-declarations`); they only
feed the type checker, which reports mismatches ahead of time. What the
checker does beyond the signature syntax itself is polymorphism, overloading
and the treatment of undeclared names.


Polymorphic predicates
========================

An uppercase name in a signature is a type variable, universally quantified.
A signature is inferred, never explicitly instantiated, so the same predicate
works at every type its rules type-check at:

.. elpi:: ../code/polymorphic.elpi
   :assert: \[3, 2, 1\] \[b, a\]

``R1`` is instantiated at ``list int``, ``R2`` at ``list string``, from the
very same ``rev``. This only happens because the signature spells out the type
variable ``A`` explicitly: the checker does not *infer* that a predicate is
polymorphic the way, say, OCaml's ``let``-polymorphism would. A predicate
with no signature at all is checked at whatever concrete types its call sites
happen to use, and a mismatch between two call sites is then a type error.


Overloading
=============

Repeating a signature with different argument types **overloads** the
predicate: the checker keeps every alternative and, at each use, picks the
one the arguments fit:

.. code-block:: elpi

   pred px int -> string.
   pred px bool -> string.
   px 0  "zero".
   px tt "true".
   px (N : int) "nonzero" :- N > 0.

``0`` and ``tt`` pin their rules to one signature each. The third rule's
``N`` does not, since an integer *or* a boolean would type-check, so it
carries a type ascription ``(N : int)`` (:doc:`../syntax/terms`). A *call*
with an unknown argument in a position where the signatures differ needs one
the same way: ``px X S`` is ambiguous, ``px (X : int) S`` is not.


Undeclared constants
======================

A constant that is used but never given a signature draws a warning naming a
signature that would fit, and the program still runs. A data constructor,
though, is a hard error the moment it is used (:doc:`../syntax/type-declarations`).
The warning is skipped for two names: the predicate called ``main``, and any
name ending in ``.aux`` or containing ``.aux.``, conventionally used for
generated or throwaway helper code that is not worth a signature.
