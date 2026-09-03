############################
Embedding and extending Elpi
############################

.. note::

   **Stub — part of the manual outline.**

   Planned content: Embedding: link with ``ocamlfind`` / ``-package elpi`` and drive the interpreter with ``API.Setup.init ~builtins``, ``API.Parse``, ``API.Compile``, ``API.Execute``, ``API.Pp`` (``elpi_REPL.ml`` is the minimal client). Extending: a full worked example of a built-in predicate written in OCaml, based on the simple ``sys.file_exists`` / ``getenv`` built-ins — the ``MLCode(Pred(…))`` FFI shape, the ``In`` / ``Out`` / ``InOut`` argument combinators, ``!:`` / ``No_clause`` / ``diagnostic``, bundling declarations into a ``BuiltIn.declaration list`` and passing it to ``Setup.init ~builtins``, and calling it from an ``.elpi`` program (shown via ``literalinclude`` of ``src/builtin.ml`` plus a short standalone driver). Also: custom data types via the FFI, registering quotations (``API.Quotation``), the extensible ``API.State``. Then defer to the odoc API reference and to coq-elpi as the large real-world embedding.

   Source material: src/API.mli; src/builtin.ml; README.md “How to embed ELPI”; HDR §3.3.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and be injected with the ``.. elpi::`` directive plus an ``:assert:`` line pinning the printed output.
