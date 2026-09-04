############
Introduction
############

Elpi is an embeddable implementation of λProlog extended with Constraint
Handling Rules (:doc:`semantics/overview`) — a logic programming language
well suited to manipulate syntax trees with binders and unification
variables. It is designed to be embedded into a larger OCaml application as
an extension language (:doc:`embedding`), with a foreign function interface
to add built-in predicates and data types. The original system description is
:ref:`Dunchev, Guidi, Sacerdoti Coen & Tassi, LPAR-20 (2015) <bib-lpar2015>`.


Why Elpi
=========

Elpi is a research project aimed at providing a programming platform for the
*elaborator* component of an interactive theorem prover — the part that turns
a term as input by the user into a well-typed one, performing type inference
and offering the user hooks to customize it (ad-hoc polymorphism, and the
like). Such a component works with terms full of binders and holes
(unification variables standing for missing information, some to be filled
to make the term well typed, some filled deliberately by an extension), which
makes it unusually demanding: the interplay of binders, reduction and
unification, plus the heuristics needed to make it practical and the hooks
needed to let users extend it, is a lot of machinery to get right from
scratch.

Elpi's answer is to make that machinery part of the language itself, rather
than something built on top of it, case by case:

* binders and substitution are native, via Higher-Order Abstract Syntax
  (:doc:`semantics/logic-programming-model`) — no de Bruijn indices to manage
  by hand;
* a hypothetical context is native too: attaching information to a bound
  variable, and collecting it back when the variable goes out of scope, is
  what ``pi``/``==>`` already do (:doc:`features/hypothetical-rules`) — a
  type checker does not maintain its own typing context, it uses Elpi's;
* the object language's own unification variables reuse the meta-language's,
  again via HOAS (:doc:`features/binders-and-hoas`) — assigning one to a term
  containing variables out of its scope, or building a circular term, is
  rejected by construction (:doc:`features/unification-and-variables`);
* the generative, backtracking search of Prolog can be turned off selectively
  by suspending a goal as a **syntactic constraint**, resumed once the
  variables it depends on are known, and inspected as a whole by constraint
  handling rules (:doc:`semantics/constraints`, :doc:`semantics/chr`) — a
  host application can extend the constraint store with its own,
  non-syntactic constraints and solvers, too;
* a rule (:doc:`syntax/inference-rules-and-queries`) can be grafted into an
  existing program, at "compile time" by accumulating a file
  (:doc:`syntax/file-structure-and-attributes`) or at run time through
  ``==>`` (:doc:`features/hypothetical-rules`).

Most of this comes from λProlog itself; constraints and constraint handling
rules are Elpi's own addition to it.


Relation to standard λProlog and to Teyjus
=============================================

Elpi is close enough to standard λProlog to run most λProlog programs
unmodified; :doc:`compatibility` collects the known lexical and semantic
differences from the Teyjus implementation. Reading
:ref:`Programming with Higher-Order Logic, by Miller and Nadathur
<bib-miller-nadathur>`, is recommended background for standard λProlog
itself — this manual assumes it and does not repeat it.


How to read this manual
=========================

This is a **reference** manual: it describes syntax and semantics feature by
feature, with runnable examples, rather than teaching λProlog from scratch.
:doc:`getting-started` is the only tutorial-shaped chapter, to get a program
running; after that, *Syntax* and *Semantics* describe the language model,
*Language features* is a feature-by-feature catalogue, *Examples* has full
worked programs, and *Libraries* / *Debugging & tooling* / *Embedding and
extending* / *Reference* round out the rest. Chapters cross-reference each
other liberally rather than repeating themselves — follow the links rather
than expecting one chapter to be self-contained.

For the full formal account of Elpi's design, see the author's
:ref:`HDR manuscript <bib-hdr>` and the papers listed in :doc:`bibliography`.

This manual is largely a recombination of that material: prose and examples
from the HDR thesis and from several of the author's own papers, reworked
into one reference organized around Elpi's syntax, semantics and features
rather than around each paper's own narrative. An AI coding assistant did
most of that reorganizing, adapting and drafting, under the author's
direction and review. The result is not as polished as the author would have
written by hand, but the AI's help in putting a document this size together
has been substantial.
