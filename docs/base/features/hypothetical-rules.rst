##################
Hypothetical rules
##################

:doc:`../syntax/inference-rules-and-queries` covers the syntax:
``H ==> G`` adds ``H`` to the program for the duration of ``G``, ``[H1, H2]
==> G`` adds several, and the traditional λProlog spelling ``=>`` means the
same thing but binds differently — this manual always uses ``==>``. This
chapter is the one thing that spelling doesn't cover: ``=!=>``.


Committing a hypothetical rule
================================

Adding a rule for a ``func`` predicate at run time can conflict with its
static rules from the determinacy checker's point of view — even when, in
practice, the new rule always fires first. ``H =!=> G`` is ``(H :- !) ==> G``:
it adds ``H`` with an automatic tail cut, so the hypothesis commits as soon as
its head matches instead of leaving a choice point the checker would have to
rule out. Because the hypothesis may only be known at run time (it can be a
variable bound to a rule computed on the fly), the cut is added dynamically
too — it is not just sugar expanded once at compile time.


Example
=======

.. elpi:: ../code/tail-cut.elpi
   :assert: copy a gives b
