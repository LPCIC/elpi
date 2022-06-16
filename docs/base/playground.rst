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

Syntax
------

Elpi code blocks to be evaluated and injection from ``docs/base`` to ``docs/source`` are conventionally denoted in ``reStructuredText`` as ``.. elpi:: FILE``.

.. literalinclude:: ../../tests/sources/chr.elpi
   :linenos:
   :language: elpi

The injection engine will:

* Retrieve all ``.. elpi::`` directives
* Change them into ``literalinclude`` in the generated source with relevant options
* Run ``dune exec elpi -- -test FILE`` on the ``FILE`` containing the ``elpi`` snippet, test or example.
* Capture its output (``stdout``)
* Create a ``code-block:: console`` just after it to inject the captured console output

Result should look as follows:

.. code-block:: console

   Parsing time: 0.000

   Compilation time: 0.004
   File "/home/jwintz/Development/elpi/tests/sources/chr.elpi", line 7, column 60, character 133: Warning: constant term has no declared type.
   File "/home/jwintz/Development/elpi/tests/sources/chr.elpi", line 11, column 8, character 319: Warning: constant len has no declared type. Did you mean std.length ?
   File "/home/jwintz/Development/elpi/tests/sources/chr.elpi", line 28, column 28, character 761: Warning: constant compatible has no declared type.

   Typechecking time: 0.154
   compat [term c1 (uvar frozen--501 []), term c0 (uvar frozen--502 [])] |- frozen--494 [
    c1, c0] arr (uvar frozen--495 [c0, c1]) (arr (uvar frozen--496 [c0, c1]) (uvar frozen--497 [])) , [
    term c3 (uvar frozen--499 []), term c2 (uvar frozen--498 [])] |- frozen--494 [
    c2, c3] arr (uvar frozen--498 []) (arr (uvar frozen--499 []) (uvar frozen--500 []))
   NEW [X0 = X1, X2 = X3] arr (X4 c0 c1) (arr (X5 c0 c1) X6) = arr X1 (arr X3 X7)
   1
   compat [term c0 bool] |- frozen--507 [c0] uvar frozen--508 [] , [term c1 (uvar frozen--509 [])] |- frozen--507 [c1] nat
   NEW [bool = X8] X9 = nat
   2
   compat [term c0 bool] |- frozen--514 [c0] uvar frozen--515 [] , [term c1 (uvar frozen--515 [])] |- frozen--514 [c1] nat
   NEW [bool = X10] X10 = nat
   compat [term c0 bool] |- frozen--520 [c0] uvar frozen--521 [] , [term c1 nat] |- frozen--520 [c1] nat
   NEW [bool = nat] X11 = nat

   Success:

   Time: 0.001

   Constraints:
    {c0} : term c0 bool ?- term (X12 c0) nat  /* suspended on X12 */ {c0 c1} : term c1 X13, term c0 X13 ?- term (X14 c1 c0) (arr X13 (arr X13 X6))  /* suspended on X14 */

   State:

Test Bed
--------

.. elpi:: ../../tests/sources/accumulated.elpi

.. elpi:: ../../tests/sources/ackermann.elpi

.. elpi:: ../../tests/sources/chr.elpi
