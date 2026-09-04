###################
Terms and operators
###################

A **term** is Elpi's data. It is built from the tokens of
:doc:`lexical-conventions` — constants, unification variables, integers,
floats and strings — by application, λ-abstraction, operators and lists.
This chapter is about the shape of terms; how terms are assembled into rules
and queries is :doc:`inference-rules-and-queries`.


Application
===========

Application is written by juxtaposition, λ-calculus style — ``f a b``, not
``f(a, b)``. For example ``node 46 (node 93 leaf leaf) leaf`` or ``F a b``.
The head is a constant or a unification variable. Each argument is a single
term — a literal or an identifier, or a *delimited* term such as a list
``[…]``, a spilled expression ``{…}``, a quotation ``{{…}}`` or a parenthesised
term. So in ``f g x`` the head ``f`` is applied to the two arguments ``g`` and
``x``; write ``f (g x)`` for the other reading.

Application binds tighter than every operator: ``f a + g b`` is
``(f a) + (g b)``.

Parentheses only group: ``(f a b)`` is the same term as ``f a b``. They are
needed only to override operator precedence — most often around ``,``, ``=>``
and ``:-`` in a rule body, see :doc:`inference-rules-and-queries`.

λ-abstraction
=============

``x\ t`` is the function that binds ``x`` in ``t``. Because the bound variable
is introduced explicitly, its name may be capitalised — ``X\ X`` is the
identity. The body extends as far to the right as possible.

.. code-block:: elpi

   x\ x                   % identity
   x\ y\ x                % first projection
   f\ a\ b\ f a b         % application, as a function

The ``\`` is always its own token: ``x\t`` and ``x \ t`` are identical.
Each ``\`` binds exactly one variable — ``x y\ z`` reads ``x (y\ z)``. The
``pi`` and ``sigma`` keywords are the exception: they take several binders at
once, so ``pi x y\ …`` reads ``pi x\ pi y\ …``. See also
:doc:`../features/binders-and-hoas`.


Operators
=========

An infix, prefix or postfix operator is just another way to write an
application: ``a + b`` is the term ``+ a b``. Precedence and associativity come
from the operator's *family* and are listed in the table in
:doc:`lexical-conventions`. To use an operator as an ordinary constant, wrap it
in parentheses:

.. elpi:: ../code/apply.elpi
   :assert: the result is 5


Lists
=====

.. code-block:: elpi

   []                % the empty list, also written  nil
   [a, b, c]         % a trailing comma is allowed:  [a, b, c,]
   [a, b | Tail]     % a list with an explicit tail
   a :: b :: []      % the same as [a, b];  ::  is also written  cons

Inside ``[ … ]`` a comma separates elements, so ``[p X, q Y]`` is a two-element
list, not a conjunction; ``[(p X, q Y)]`` is a one-element list whose element is
a conjunction.

The names ``nil`` and ``cons`` are accepted for ``[]`` and ``::``.

Type ascription
===============

``(t : ty)`` annotates ``t`` with a type. It is read by the type checker and
has no effect at run time.

.. code-block:: elpi

   Empty = ([] : list int)

A binder may carry a type ascription too: ``x : ty\ t``.

Naming a subterm with ``as``
============================

``(t as N)`` binds ``N`` to the term ``t`` — the parentheses are required and
``as`` takes everything to its left. It names a part of a rule head so the rest
of the rule can refer to it; see :doc:`inference-rules-and-queries`.

.. code-block:: elpi

   copy (lam F as L) L :- ...


Braces
======

``{ t }`` is *spilling* — it lifts the call ``t`` out to just before the
enclosing goal; see :doc:`../features/spilling`. ``{{ t }}`` is a *quotation*,
custom syntax that a host application translates into a term; see
:doc:`../features/quotations`.

Example
=======

.. elpi:: ../code/terms.elpi
   :assert: leaves: 3 pair: \[leaf, leaf\]
