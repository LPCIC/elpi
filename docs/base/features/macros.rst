######
Macros
######

``macro @name Args :- Body.`` (:doc:`../syntax/file-structure-and-attributes`)
is expanded at compile time; a macro is never a predicate and leaves no trace
at run time. This chapter is what that buys.


Hygiene
========

A macro's own variables — the ones in ``Body`` that are not among ``Args`` —
get a fresh instance at *every* expansion, distinct from whatever else is in
scope at the use site, even a variable spelled exactly the same way (see the
Example below). Writing a macro is therefore as safe as writing a predicate
with a fresh set of local variables — no need to pick unlikely names to avoid
clashing with whatever calls it.


Factoring a repeated pattern
===============================

A macro is a natural way to name a recurring combination of goals — for
instance, the pairing of "typed" and "pretty-printed" that a hypothetical
rule (:doc:`hypothetical-rules`) needs at every bound variable of a term with
binders:

.. code-block:: elpi

   macro @of X N T :- (of X T, pp X N).

   of (lambda Name F) (arr A B) :-
     pi x\ @of x Name A => of (F x) B.

Every occurrence of ``@of x Name A`` expands to ``of x A, pp x Name`` right
there, so the two rules that must always be added together cannot drift
apart as the code around them changes.


Example
=======

.. elpi:: ../code/macro-hygiene.elpi
   :assert: macro's Tmp = 5\ncaller's Tmp is still 999
