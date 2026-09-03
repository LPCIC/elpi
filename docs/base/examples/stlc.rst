#############################
Simply-typed λ-calculus
#############################

.. note::

   **Stub — part of the manual outline.**

   Planned content: The “hello world” of λProlog: the ``term`` data type with HOAS (``app``, ``fun``); weak-head reduction (``whd``); the type checker (``of``) using ``pi x\ … ==> …``; running it on ``λx.λy.x`` and on the untypable ``λx.(x x)`` (occur-check failure).

   Source material: coq-elpi tutorial “Terms with binders”; HDR §2.2.

The program
===========

``term`` is represented with higher-order abstract syntax: ``fun`` carries a
λProlog function, so substitution is application. ``whd`` is weak-head
reduction; ``of`` is the type checker, which goes under ``fun`` with ``pi`` and
adds the hypothetical rule ``of x A`` with ``==>``. The query types
``λx.λy.x``:

.. elpi:: ../code/stlc.elpi
   :assert: type of Fst: arr X0 \(arr X1 X0\)
