######################################
Compatibility with Teyjus and Prolog
######################################

.. note::

   **Stub — part of the manual outline.**

   Planned content:

   * The known incompatibilities with Teyjus and standard λProlog: semantics and modules (from ``INCOMPATIBILITIES.md``). Lexical differences are already covered in :doc:`syntax/lexical-conventions` (“Relation to Teyjus”).
   * The older signature forms kept for compatibility: ``type name … -> prop``, the ``mode (name i o)`` directive and the ``i:`` / ``o:`` argument markers — how they map onto the modern ``pred`` / ``func`` ``In.. -> Out..`` signatures, and the one case still needed today (``:functional pred name o:.., i:..`` for a signature whose input and output arguments are interleaved).
   * The ``:nooc`` attribute: unification does an occur check by default (Prolog does not); ``:nooc`` turns it off for one predicate. Example from the standard library, ``std.unsound_unif``:

     .. code-block:: elpi

        % Unification without occur check. It can create infinite terms.
        :nooc
        func unsound_unif -> A, A.
        unsound_unif X X.

     Guard code that disables the occur check against building cyclic terms with ``ground_term``. See also *Unification and variables*.

   Source material: ``INCOMPATIBILITIES.md``; ``src/builtin_stdlib.elpi``; ELPI.md “Mode and type declaration” / “Occur check”.
