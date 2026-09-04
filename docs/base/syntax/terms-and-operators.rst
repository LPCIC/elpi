###################
Terms and operators
###################

A **term** is Elpi's data. It is built from the tokens of
:doc:`lexical-conventions` — constants, unification variables, integers,
floats and strings — by application, operators, lists and λ-abstraction.
This chapter is about the shape of terms; how terms are assembled into rules
and queries is :doc:`rules-and-queries`.


Application
===========

Application is written by juxtaposition, λ-calculus style — ``f a b``, not
``f(a, b)``:

.. code-block:: elpi

   node 46 (node 93 leaf leaf) leaf

The head (``node`` here) is a constant or a unification variable — a variable
head is a higher-order application, ``F a b``. Each argument is a single
*closed* term: a constant, a literal, a list, a ``{…}`` / ``{{…}}`` group, or a
parenthesised term. So in ``f g x`` the head ``f`` is applied to the two
arguments ``g`` and ``x``; write ``f (g x)`` for the other reading.

Application binds tighter than every operator: ``f a + g b`` is
``(f a) + (g b)``.

Parentheses only group; ``(f a b)`` and ``f a b`` are the same term. The one
place they matter is around ``,``, ``;``, ``=>``, ``==>`` and ``:-`` — see
:doc:`rules-and-queries`.


Operators
=========

An infix, prefix or postfix operator is just another way to write an
application: ``a + b`` is the term ``+ a b``. Precedence and associativity come
from the operator's *family* and are listed in the table in
:doc:`lexical-conventions`. To use an operator as an ordinary constant, wrap it
in parentheses:

.. code-block:: elpi

   Apply = (F\ A\ B\ F A B),
   S is Apply (+) 2 3           % S = 5

Elpi has no ``infix`` / ``prefix`` directive: the set of operators is fixed.


Lists
=====

.. code-block:: elpi

   []                % the empty list, also written  nil
   [a, b, c]         % a trailing comma is allowed:  [a, b, c,]
   [a, b | Tail]     % a list with an explicit tail
   a :: b :: []      % the same as [a, b];  ::  is also written  cons

Inside ``[ … ]`` a comma separates elements, so ``[p X, q Y]`` is a
two-element list, not a conjunction.


λ-abstraction
=============

``x\ t`` is the function that binds ``x`` in ``t``. Because the bound variable
is introduced explicitly, its name may be capitalised — ``X\ X`` is the
identity. The body extends as far to the right as possible.

.. code-block:: elpi

   x\ x                   % identity
   x\ y\ x                % first projection;  x y\ x  is the same
   f\ a\ b\ f a b         % application, as a function

The ``\`` is always its own token: ``x\t`` and ``x \ t`` are identical.
``pi`` and ``sigma`` are binders too (``pi x y\ …``) and are covered in
:doc:`../features/binders-and-hoas`. A binder may carry a type,
``x : ty\ t``.


Type ascription
===============

``(t : ty)`` annotates ``t`` with a type. It is read by the type checker and
has no effect at run time.

.. code-block:: elpi

   Empty = ([] : list int)


Naming a subterm with ``as``
============================

``(t as N)`` binds ``N`` to the term ``t`` — the parentheses are required and
``as`` takes everything to its left. It is used almost exclusively to name a
part of a rule head so the rest of the rule can refer to it; see
:doc:`rules-and-queries`.

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
