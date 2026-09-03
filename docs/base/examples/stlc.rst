#######################
Simply-typed λ-calculus
#######################

.. note::

   **Stub — part of the manual outline.**

   Planned content: The “hello world” of λProlog: the ``term`` data type with HOAS (``app``, ``fun``); weak-head reduction (``whd``); the type checker (``of``) using ``pi x\ … ==> …``; running it on ``λx.λy.x`` and on the untypable ``λx.(x x)`` (occur-check failure).

   Source material: coq-elpi tutorial “Terms with binders”; HDR §2.2.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and be injected with the ``.. elpi::`` directive plus an ``:assert:`` line pinning the printed output.
