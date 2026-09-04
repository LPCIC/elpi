##########
Quotations
##########

``{{ … }}`` (the *default* quotation) and ``{{:name … }}`` (a *named* one,
``name`` any run of non-space characters) let a term be written in a
different, custom syntax and turned into an Elpi term at compile time. A
quotation is not built in: a host application registers each one it wants
through the OCaml API (:doc:`../embedding`), by giving Elpi a parser from
source text to a term. With none registered, ``{{ … }}`` is a compile-time
error ("No default quotation").


A worked, self-testing quotation
===================================

For its own testing the ``elpi`` command line tool registers one named
quotation, also called ``elpi``, whose "custom syntax" is just Elpi syntax
itself — it parses the quoted text as an ordinary term and hands it back
unevaluated (see the Example below). This is enough to see the *mechanism* —
a chunk of foreign-looking source turning into a term the surrounding program
can inspect and build upon — even though the "foreign" language here happens
to be Elpi.


Antiquotation
===============

A quotation can embed a piece of the *surrounding* Elpi program inside the
foreign syntax — an antiquotation. There is no single antiquotation syntax:
it is whatever the quotation's own parser decides to recognise. coq-elpi, for
instance, quotes Rocq's term syntax and antiquotes back to Elpi with an
``lp:`` prefix:

.. code-block:: text

   prod "x" t x\ {{ nat -> lp:x * bool }}

Here ``lp:x`` splices the Elpi variable ``x`` — bound just outside the
quotation — into the quoted Rocq term.


Example
=======

.. elpi:: ../code/quotation.elpi
   :assert: 1 \+ 2
