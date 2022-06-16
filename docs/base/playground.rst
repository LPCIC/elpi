Playground
==========

This page will be used to test hooks in order to run ``elpi`` on code snippets and inject its output within ``sphinx`` documentation sources.

Prerequisites
-------------

Before running the hooks, make sure to have ``elpi`` built locally:

.. code-block:: console

   eval $(opam env)
   make build

It doesn't hurt to check that ``dune`` runs the locally built ``elpi`` correctly:

.. code-block:: console

   dune exec elpi -- -h
