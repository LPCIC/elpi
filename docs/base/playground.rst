Playground
==========

This page is used to test hooks in order to run ``elpi`` on code snippets and inject its output within ``sphinx`` documentation sources.

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

Elpi code blocks to be evaluated and which output is to be injected from ``docs/base`` to ``docs/source`` are conventionally denoted in ``reStructuredText`` as ``.. elpi:: FILE``.

.. literalinclude:: ../../tests/sources/chr.elpi
   :linenos:
   :language: elpi

The injection engine:

* Retrieves all ``.. elpi::`` directives
* Changes them into ``literalinclude`` in the generated source with relevant options
* Runs ``dune exec elpi -- -test FILE`` on the ``FILE`` containing the ``elpi`` snippet, test or example.
* Captures its output (``stdout``)
* Creates a ``code-block:: console`` just after it to inject the captured console output
* Captures its output (``stderr``)
* Creates a ``code-block:: console`` just after it to inject the captured console erros
* In case of an assertion option for the ``elpi`` directive, the output is injected only if matched

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

Regexp Matching
---------------

This ``elpi`` directive should pass validation:

.. code-block:: console
   
   .. elpi:: ./a.elpi
      :assert: V = s \(.*\)

.. elpi:: ./a.elpi
   :assert: V = s \(.*\)

This one should fail validation, only a message stating the regexp matching error will be printed:

.. code-block:: console
   
   .. elpi:: ./a.elpi
      :assert: /(?!)/

.. elpi:: ./a.elpi
   :assert: /(?!)/

Test Bed
--------

.. elpi:: ../../tests/sources/accumulate_twice1.elpi
.. elpi:: ../../tests/sources/accumulate_twice2.elpi
.. elpi:: ../../tests/sources/accumulated.elpi
.. elpi:: ../../tests/sources/ackermann.elpi
.. elpi:: ../../tests/sources/asclause.elpi
.. elpi:: ../../tests/sources/beta.elpi
.. elpi:: ../../tests/sources/block.elpi
.. elpi:: ../../tests/sources/chr.elpi
.. elpi:: ../../tests/sources/chrGCD.elpi
.. elpi:: ../../tests/sources/chrLEQ.elpi
.. elpi:: ../../tests/sources/chr_nokey.elpi
.. elpi:: ../../tests/sources/chr_nokey2.elpi
.. elpi:: ../../tests/sources/chr_not_clique.elpi
.. elpi:: ../../tests/sources/chr_sem.elpi
.. elpi:: ../../tests/sources/conj2.elpi
.. elpi:: ../../tests/sources/ctx_loading.elpi
.. elpi:: ../../tests/sources/cut.elpi
.. elpi:: ../../tests/sources/cut2.elpi
.. elpi:: ../../tests/sources/cut3.elpi
.. elpi:: ../../tests/sources/cut4.elpi
.. elpi:: ../../tests/sources/cut5.elpi
.. elpi:: ../../tests/sources/cut6.elpi
.. elpi:: ../../tests/sources/deep_indexing.elpi
.. elpi:: ../../tests/sources/discard.elpi
.. elpi:: ../../tests/sources/elpi_only_llam.elpi
.. elpi:: ../../tests/sources/end_comment.elpi
.. elpi:: ../../tests/sources/eta.elpi
.. elpi:: ../../tests/sources/eta_as.elpi
.. elpi:: ../../tests/sources/even-odd.elpi
.. elpi:: ../../tests/sources/findall.elpi
.. elpi:: ../../tests/sources/fragment_exit.elpi
.. elpi:: ../../tests/sources/fragment_exit2.elpi
.. elpi:: ../../tests/sources/fragment_exit3.elpi
.. elpi:: ../../tests/sources/general_case.elpi
.. elpi:: ../../tests/sources/general_case2.elpi
.. elpi:: ../../tests/sources/general_case3.elpi
.. elpi:: ../../tests/sources/hc_interp.elpi
.. elpi:: ../../tests/sources/hdclause.elpi
.. elpi:: ../../tests/sources/heap_discard.elpi
.. elpi:: ../../tests/sources/ho.elpi
.. elpi:: ../../tests/sources/hollight.elpi
.. elpi:: ../../tests/sources/hollight_legacy.elpi
.. elpi:: ../../tests/sources/hyp_uvar.elpi
.. elpi:: ../../tests/sources/impl.elpi
.. elpi:: ../../tests/sources/impl2.elpi
.. elpi:: ../../tests/sources/index2.elpi
.. elpi:: ../../tests/sources/io_colon.elpi
.. elpi:: ../../tests/sources/lambda.elpi
.. elpi:: ../../tests/sources/lambda2.elpi
.. elpi:: ../../tests/sources/lambda3.elpi
.. elpi:: ../../tests/sources/list_as_conj.elpi
.. elpi:: ../../tests/sources/list_comma.elpi
.. elpi:: ../../tests/sources/llam.elpi
.. elpi:: ../../tests/sources/llamchr.elpi
.. elpi:: ../../tests/sources/map.elpi
.. elpi:: ../../tests/sources/map_list.elpi
.. elpi:: ../../tests/sources/map_list_opt.elpi
.. elpi:: ../../tests/sources/name_builtin.elpi
.. elpi:: ../../tests/sources/named_clauses00.elpi
.. elpi:: ../../tests/sources/named_clauses01.elpi
.. elpi:: ../../tests/sources/named_clauses02.elpi
.. elpi:: ../../tests/sources/namespaces00.elpi
.. elpi:: ../../tests/sources/namespaces01.elpi
.. elpi:: ../../tests/sources/namespaces02.elpi
.. elpi:: ../../tests/sources/namespaces03.elpi
.. elpi:: ../../tests/sources/nil_cons.elpi
.. elpi:: ../../tests/sources/notation.elpi
.. elpi:: ../../tests/sources/notation_error.elpi
.. elpi:: ../../tests/sources/notation_legacy.elpi
.. elpi:: ../../tests/sources/patternunif.elpi
.. elpi:: ../../tests/sources/patternunif2.elpi
.. elpi:: ../../tests/sources/pi.elpi
.. elpi:: ../../tests/sources/pi3.elpi
.. elpi:: ../../tests/sources/pi5.elpi
.. elpi:: ../../tests/sources/pnf.elpi
.. elpi:: ../../tests/sources/polymorphic_variants.elpi
.. elpi:: ../../tests/sources/printer.elpi
.. elpi:: ../../tests/sources/queens.elpi
.. elpi:: ../../tests/sources/quote_syntax.elpi
.. elpi:: ../../tests/sources/random.elpi
.. elpi:: ../../tests/sources/reduce_cbn.elpi
.. elpi:: ../../tests/sources/reduce_cbv.elpi
.. elpi:: ../../tests/sources/restriction.elpi
.. elpi:: ../../tests/sources/restriction3.elpi
.. elpi:: ../../tests/sources/restriction4.elpi
.. elpi:: ../../tests/sources/restriction5.elpi
.. elpi:: ../../tests/sources/restriction6.elpi
.. elpi:: ../../tests/sources/rev.elpi
.. elpi:: ../../tests/sources/rev14.elpi
.. elpi:: ../../tests/sources/same_term.elpi
.. elpi:: ../../tests/sources/self_assignment.elpi
.. elpi:: ../../tests/sources/set.elpi
.. elpi:: ../../tests/sources/shorten.elpi
.. elpi:: ../../tests/sources/shorten2.elpi
.. elpi:: ../../tests/sources/shorten_aux.elpi
.. elpi:: ../../tests/sources/shorten_aux2.elpi
.. elpi:: ../../tests/sources/shorten_builtin.elpi
.. elpi:: ../../tests/sources/shorten_trie.elpi
.. elpi:: ../../tests/sources/spill_and.elpi
.. elpi:: ../../tests/sources/spill_impl.elpi
.. elpi:: ../../tests/sources/spill_lam.elpi
.. elpi:: ../../tests/sources/trace.elpi
.. elpi:: ../../tests/sources/trace2.elpi
.. elpi:: ../../tests/sources/trace_chr.elpi
.. elpi:: ../../tests/sources/trace_cut.elpi
.. elpi:: ../../tests/sources/trace_findall.elpi
.. elpi:: ../../tests/sources/trail.elpi
.. elpi:: ../../tests/sources/typeabbrv.elpi
.. elpi:: ../../tests/sources/typeabbrv1.elpi
.. elpi:: ../../tests/sources/typeabbrv10.elpi
.. elpi:: ../../tests/sources/typeabbrv11.elpi
.. elpi:: ../../tests/sources/typeabbrv12.elpi
.. elpi:: ../../tests/sources/typeabbrv2.elpi
.. elpi:: ../../tests/sources/typeabbrv3.elpi
.. elpi:: ../../tests/sources/typeabbrv4.elpi
.. elpi:: ../../tests/sources/typeabbrv5.elpi
.. elpi:: ../../tests/sources/typeabbrv6.elpi
.. elpi:: ../../tests/sources/typeabbrv7.elpi
.. elpi:: ../../tests/sources/typeabbrv8.elpi
.. elpi:: ../../tests/sources/typeabbrv9.elpi
.. elpi:: ../../tests/sources/uminus.elpi
.. elpi:: ../../tests/sources/uvar_chr.elpi
.. elpi:: ../../tests/sources/var.elpi
.. elpi:: ../../tests/sources/variadic_declare_constraints.elpi
.. elpi:: ../../tests/sources/w.elpi
.. elpi:: ../../tests/sources/w_legacy.elpi
.. elpi:: ../../tests/sources/zebra.elpi