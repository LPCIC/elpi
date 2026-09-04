###########################
Input and output arguments
###########################

.. note::

   **Stub — part of the manual outline.**

   Planned content: The ``In.. -> Out..`` split in a ``pred`` / ``func`` signature; what *input* means operationally — the corresponding goal argument is matched against the pattern in the rule head and is never assigned, so unification variables inside it survive the call; the ``uvar`` pattern and ``uvar as N`` for matching a flexible input; a pure relation is written ``pred name -> Out..`` (no inputs). The standalone ``mode`` directive is in *Compatibility with Teyjus and Prolog*.

   Source material: ELPI.md “Modes”; HDR §2.3; coq-elpi tutorial “Modes and matching”.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and be injected with the ``.. elpi::`` directive plus an ``:assert:`` line pinning the printed output.
