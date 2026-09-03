############
Introduction
############

Elpi is an embeddable implementation of λProlog extended with Constraint
Handling Rules. λProlog is the logic programming
language built on higher-order hereditary Harrop formulas described by
:ref:`Miller and Nadathur <bib-miller-nadathur>`. Constraint Handling Rules
(:ref:`Sneyers et al. <bib-chr-survey>`) are a rule-based formalism for
rewriting a store of constraints, adding to it, removing from it and combining
its elements, which Elpi puts to work inspecting and simplifying goals it
has set aside for later.

Like every logic programming language Elpi computes by proof search, but its
terms are those of the simply-typed λ-calculus rather than first-order trees.
That is what makes it well suited to manipulating syntax trees that contain
binders and unification variables, the *holes* that stand for information
not yet known.

Elpi is designed to be embedded into a larger OCaml application as an
extension language. A foreign function interface lets the host application
contribute its own built-in predicates and data types, so that Elpi programs
can call back into OCaml and exchange values with it.

The original system is described by :ref:`Dunchev, Guidi, Sacerdoti Coen &
Tassi, LPAR-20 (2015) <bib-lpar2015>`.


Why Elpi
=========

Elpi is a research project aimed at providing a programming platform for the
*elaborator* component of an interactive theorem prover, the part that turns
a term as input by the user into a well-typed one, performing type inference
and offering the user hooks to customize it (ad-hoc polymorphism, and the
like). Such a component works with terms full of binders and holes:
unification variables standing for missing information, some to be filled in
so that the term type-checks, some filled deliberately by an extension. This
makes it unusually demanding to write. The interplay of binders, reduction
and unification is delicate on its own; on top of it come the heuristics that
make the elaborator practical and the hooks that let users extend it. That is
a large amount of machinery to get right from scratch, and every prover that
builds it from scratch builds a slightly different, slightly incompatible
version of it.

Elpi's answer is to make that machinery part of the language itself, rather
than something each application rebuilds on top of it:

* binders and substitution are native, through Higher-Order Abstract Syntax
  (:doc:`features/binders-and-hoas`): an object-language binder is
  represented by a meta-language λ-abstraction, so capture-avoiding
  substitution is ordinary β-reduction and there are no de Bruijn indices to
  shift by hand;
* a hypothetical context is native too. Attaching information to a bound
  variable, and discarding it again when that variable goes out of scope, is
  what ``pi`` and ``==>`` already do
  (:doc:`syntax/inference-rules-and-queries`): a type checker written in Elpi
  does not maintain its own typing context, it uses Elpi's;
* the object language's own unification variables can reuse the
  meta-language's, once more through HOAS
  (:doc:`features/binders-and-hoas`), so that instantiating a hole in the
  object term is instantiating an Elpi variable;
* the generative, backtracking search inherited from Prolog can be switched
  off selectively: a goal is suspended as a *syntactic constraint*, resumed
  only once the variables it waits on are known, and then inspected as a
  whole by constraint handling rules (:doc:`semantics/constraints`,
  :doc:`semantics/chr`). A host application can extend the constraint store
  with constraints and solvers of its own, which need not be syntactic;
* a rule (:doc:`syntax/inference-rules-and-queries`) can be grafted into an
  existing program either at compile time, by accumulating a file
  (:doc:`syntax/file-structure-and-attributes`), or at run time, through
  implication (:doc:`syntax/inference-rules-and-queries`).

Most of this Elpi inherits from λProlog; the constraints and the constraint
handling rules are its own addition.


Relation to standard λProlog and to Teyjus
=============================================

Elpi stays close enough to standard λProlog to run most λProlog programs
unmodified. :doc:`compatibility` collects the lexical and semantic points on
which it knowingly departs from the earlier Teyjus implementation, together
with the older Elpi spellings that newer ones have since replaced. For
λProlog itself, :ref:`Programming with Higher-Order Logic, by Miller and
Nadathur <bib-miller-nadathur>` is the recommended background: this manual
assumes it throughout and does not re-teach it.


How to read this manual
=========================

This is a reference manual. It describes Elpi's syntax and semantics feature
by feature, each point illustrated by a runnable example, rather than
teaching λProlog from first principles. The one tutorial-shaped chapter is
:doc:`getting-started`, which covers just enough to get a program running.
After it, the parts of the manual are:

* *Syntax* and *Semantics* describe the language model: *Syntax* as the
  concrete surface notation, *Semantics* as the computation that notation
  denotes;
* *Language features* is the feature-by-feature catalogue; each entry gives
  the syntax, the operational meaning, the flags that affect it and the
  caveats;
* *Examples* collects full worked programs;
* *Libraries*, *Debugging & tooling*, *Embedding and extending* and
  *Reference* cover the remaining ground.

Chapters cross-reference one another freely rather than repeating material,
so following the links is part of reading the manual; no single chapter is
meant to stand entirely on its own. For the full formal account of Elpi's
design, see the author's :ref:`HDR manuscript <bib-hdr>` and the papers
listed in :doc:`bibliography`.

This manual is largely a recombination of that material: prose and examples
drawn from the HDR thesis and from several of the author's own papers,
reworked into a single reference organized around Elpi's syntax, semantics
and features rather than around each paper's own narrative. The result is not
as polished as the author would have written entirely by hand, but the help
of an AI agent in putting a document this size together, under the author's
direction and review, has been substantial.
