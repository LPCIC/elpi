#############
Bibliography
#############

.. _bib-hdr:

Enrico Tassi, `Elpi: rule-based extension language
<https://inria.hal.science/hal-05294918>`_, HDR thesis (9 January 2026). The
most complete account of Elpi's design and its applications; the primary
source for this manual's *Semantics* part.

.. _bib-padl2026:

Davide Fissore and Enrico Tassi, `Determinacy Checking for Elpi: an
Higher-Order Logic Programming language with Cut
<https://inria.hal.science/hal-05026472>`_, PADL 2026 (LNCS 16401). The
formal treatment behind :doc:`features/determinacy-checking`.

.. _bib-lpar2015:

Cvetan Dunchev, Ferruccio Guidi, Claudio Sacerdoti Coen and Enrico Tassi,
`ELPI: Fast, Embeddable, λProlog Interpreter
<https://inria.hal.science/hal-01176856>`_, LPAR-20 (2015). The original
system description; cite this one for Elpi itself.

.. _bib-chr2004:

Gregory J. Duck, Peter J. Stuckey, María García de la Banda and Christian
Holzbaur, `The Refined Operational Semantics of Constraint Handling Rules
<https://doi.org/10.1007/978-3-540-27775-0_7>`_, Logic Programming (ICLP
2004), Springer, pages 90–104. The paper that names and defines the refined
operational semantics Elpi implements for CHR, the finer, still
non-deterministic-from-the-user's-view semantics behind
:doc:`semantics/chr` and :doc:`semantics/formal-semantics`.

.. _bib-chr-survey:

Jon Sneyers, Peter Van Weert, Tom Schrijvers and Leslie De Koninck, `As time
goes by: Constraint Handling Rules — A survey of CHR research from 1998 to
2007 <https://arxiv.org/abs/0906.4474>`_, Theory and Practice of Logic
Programming 10(1), 2010, pages 1–47. A broad survey of CHR as a
general-purpose declarative formalism: its semantics, program analysis,
implementations, extensions and applications; cited from :doc:`introduction`
for what CHR is.

.. _bib-tassi2019:

Ferruccio Guidi, Claudio Sacerdoti Coen and Enrico Tassi, `Implementing type
theory in higher order constraint logic programming
<https://hal.inria.fr/hal-01410567v2>`_, Mathematical Structures in Computer
Science 29(8), 2019. Constraints and constraint handling rules, formally;
cited throughout :doc:`semantics/chr` and :doc:`semantics/formal-semantics`
as ``TASSI_2019``.

.. _bib-mlws18:

Enrico Tassi, `Elpi: an extension language with binders and unification
variables <https://github.com/gares/mlws18/blob/master/slides.pdf>`_, slides
from the ML Family Workshop 2018. A lightweight, slide-shaped introduction;
its companion code, `toyml <https://github.com/gares/mlws18/tree/master/toyml>`_,
implements Algorithm W in Elpi and is a second, independent take on
:doc:`examples/hindley-milner`.

.. _bib-miller91:

Dale Miller, `A logic programming language with lambda-abstraction, function
variables, and simple unification
<https://doi.org/10.1093/logcom/1.4.497>`_, Journal of Logic and Computation
1(4), 1991, pages 497–536. Introduces the higher-order pattern fragment (Lλ)
that Elpi restricts unification variables to; see
:doc:`features/unification-and-variables`.

.. _bib-miller92:

Dale Miller, `Unification under a mixed prefix
<https://doi.org/10.1016/0747-7171(92)90011-R>`_, Journal of Symbolic
Computation 14(4), 1992, pages 321–358. The most-general-extension property
behind the ``unify`` function of :doc:`semantics/formal-semantics`.

.. _bib-miller-nadathur:

Dale Miller and Gopalan Nadathur, *Programming with Higher-Order Logic*,
Cambridge University Press, 2012. The reference for standard λProlog, which
this manual assumes throughout rather than re-teaching
(:doc:`introduction`).

.. _bib-bprolog:

Neng-Fa Zhou, `The Language Features and Architecture of B-Prolog
<https://arxiv.org/abs/1103.0812>`_, Theory and Practice of Logic Programming
12(1–2), 2012, pages 189–218. Introduces B-Prolog's *matching clauses*, whose
one-way head matching is the idea behind Elpi's input-mode arguments; see
:doc:`semantics/logic-programming-model` and :doc:`semantics/constraints`.

.. _bib-michaylov:

Spiro Michaylov and Frank Pfenning, `Higher-Order Logic Programming as
Constraint Logic Programming <https://api.semanticscholar.org/CorpusID:9980455>`_,
Proceedings of the First Workshop on Principles and Practice of Constraint
Programming, Brown University, 1993, pages 221–229. Reads a higher-order
logic programming language as a constraint logic programming one; the
constraint-resume rule of :doc:`semantics/formal-semantics` follows it.
