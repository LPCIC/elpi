#####
Terms
#####

A term is Elpi's data: the goals it runs, the rules it stores and the values
it computes are all terms. A term is built from the tokens of
:doc:`lexical-conventions` (constants, unification variables, integers, floats
and strings) by four constructions: application, λ-abstraction, operators and
lists. Assembling terms into rules and queries is discussed in
:doc:`inference-rules-and-queries`.


Application
===========

Application is written by juxtaposition, λ-calculus style: ``f a b``, never
``f(a, b)``. Longer examples are ``node 46 (node 93 leaf leaf) leaf`` and
``F a b``, the latter with a unification variable in head position.

The head of an application, its leftmost term, must be a constant or a
unification variable. The parser rejects anything else, so ``(x\ t) a`` is a
syntax error, not a β-redex written by hand. β-redexes still occur, but only
at run time, once a variable in head position has been bound to a
λ-abstraction.

Each argument is a single term: a literal or an identifier, or a *delimited*
term (a list ``[…]``, a spilled expression ``{…}``, a quotation ``{{…}}`` or
a parenthesised term). Nothing wider than that is an argument, so in ``f g x``
the head ``f`` is applied to the two separate arguments ``g`` and ``x``;
write ``f (g x)`` for the reading in which ``g x`` is one argument.

Application binds tighter than every operator: ``f a + g b`` is
``(f a) + (g b)``, not ``f (a + g) b``.

Parentheses only group; they build no term of their own, so ``(f a b)`` is
the very same term as ``f a b``. They are needed only to override the
precedence of an operator, most often around ``,`` and ``:-`` in a rule
body, see :doc:`inference-rules-and-queries`.


λ-abstraction
=============

``x\ t`` is the function that binds ``x`` in ``t``. Because the ``\``
introduces the bound variable explicitly, its name may be capitalised without
being read as a unification variable, so ``X\ X`` is the identity function.
The body extends as far to the right as possible, so ``x\ f x`` is
``x\ (f x)``.

.. code-block:: elpi

   x\ x                   % identity
   x\ y\ x                % first projection
   f\ a\ b\ f a b         % application, as a function

The ``\`` is always a token on its own: ``x\t``, ``x \t`` and ``x \ t`` are
all the same. Each ``\`` binds one variable, so ``x y\ z`` reads
``x (y\ z)``, an application whose argument is a function. The ``pi`` and
``sigma`` quantifiers are the one exception: each takes several binders at
once, so ``pi x y\ …`` reads ``pi x\ pi y\ …``. Binders, their scope, and how
Elpi uses them to represent object-language binders are covered in
:doc:`../features/binders-and-hoas`.


Operators
=========

An infix, prefix or postfix operator is another notation for an application:
``a + b`` *is* the term ``+ a b``. Which symbols are operators, and with what
precedence and associativity, is fixed by the language; the table is in
:doc:`lexical-conventions`. To use an operator as an ordinary constant, say to
pass it as an argument or give it a rule, wrap it in parentheses. Here ``(+)`` is the bare constant behind ``a + b``, passed as the
first argument of a higher-order ``Apply``:

.. elpi:: ../code/apply.elpi
   :assert: the result is 5


Lists
=====

.. code-block:: elpi

   []                % the empty list, also written  nil
   [a, b, c]         % a trailing comma is allowed:  [a, b, c,]
   [a, b | Tail]     % a partial list: the elements a and b, then a tail
   a :: b :: []      % the same as [a, b];  ::  is also written  cons

``[a, b, c]`` is sugar for ``a :: b :: c :: []``, that is
``cons a (cons b (cons c nil))``. The term after ``|`` is arbitrary: ``[a | X]``
is ``cons a X``, and ``X`` need not be a list yet; it may be an unbound
variable that a later goal fills in.

Inside ``[ … ]`` a comma separates elements; it is not the conjunction
operator. ``[p X, q Y]`` is a two-element list, whereas ``[(p X, q Y)]`` is a
one-element list whose single element is a conjunction.


Type ascription
===============

``(t : ty)`` annotates ``t`` with the type ``ty``; the parentheses are part
of the form. The annotation is read by the type checker and has no effect at
run time. Its purpose is to resolve an overloaded name, or to pin down a
polymorphic term the checker would otherwise leave ambiguous:

.. code-block:: elpi

   Empty = ([] : list int)

A binder may carry an ascription on the variable it introduces, and there the
parentheses are dropped: ``x : ty\ t`` binds ``x`` at type ``ty``, with body
``t`` (the ``:`` groups with the variable, not the body). Adding the
parentheses, ``(x : ty)\ t``, is a parse error, since ``(x : ty)`` is then the
cast form above, which is not a binder.


Naming a subterm with ``as``
============================

``(t as N)`` binds ``N`` to the term ``t``. The parentheses are required, and
``as`` takes everything to its left as ``t``. It is used in a rule head to
give a name to a part of the matched term, so the body can refer to that part
without spelling it out a second time:

.. code-block:: elpi

   sort ([X, Y] as L) L :- X < Y.   % a two-element list, already sorted

Matching this head against a goal binds ``L`` to the whole first argument and,
at the same time, ``X`` and ``Y`` to its two elements.


Braces
======

``{ t }`` is *spilling*: it lifts the call ``t`` out of the term it sits in,
runs it just before the enclosing goal, and leaves ``t``'s output argument in
its place. It is shorthand for functional-style code and is described in
:doc:`../features/spilling`.

``{{ t }}`` is a *quotation*: custom syntax, delimited by the double braces,
that a host application parses and turns into a term of its own choosing. See
:doc:`../embedding`.

Application, a list term and a lambda term in one small program:

.. elpi:: ../code/terms.elpi
   :assert: leaves: 3 pair: \[leaf, leaf\]
