#########################
Constraint Handling Rules
#########################

.. note::

   **Stub — part of the manual outline.**

   Planned content: The constraint store as a multiset of sequents ``E ▷ Γ ⊢ c``; frozen unification variables and the ``uvar K [args]`` reification presented to rules; simpagation ``keep \ remove | guard <=> new`` and its logical reading; context filters ``r s ?- p q { … }`` and cliques; trigger overlap, clusters and the inert ``_`` trigger; the refined operational semantics; a global state built on CHR; the symmetric-rule / multiset subtlety.

   Source material: HDR §2.4, §2.5.1, §2.8.4; ELPI.md “Syntactic constraints”; coq-elpi tutorial “Constraint Handling Rules”.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and be injected with the ``.. elpi::`` directive plus an ``:assert:`` line pinning the printed output.
