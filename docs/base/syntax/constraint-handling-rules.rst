#########################
Constraint handling rules
#########################

.. note::

   **Stub — part of the manual outline.**

   Planned content: the concrete syntax of constraints and Constraint Handling
   Rules. The execution model — the constraint store, simpagation, resumption —
   is covered separately in the *Semantics* part (*Constraint handling rules*).

   The ``declare_constraint`` builtin and its trigger list; suspending a goal
   and resuming it. The ``constraint <context filter> ?- <clique> { rule … }``
   block. CHR rule syntax: ``rule TO-MATCH \ TO-REMOVE | GUARD <=> TO-ADD`` —
   the ``keep \ remove`` simpagation split, the ``| guard`` and
   ``<=> new-goals`` parts, ``:name`` and ``:if`` on a rule. Sequent patterns
   ``(E : Ctx ?- Goal)`` and the ``?-`` separator. Cliques and context filters.

   Source material: ELPI.md ("Syntactic constraints", "Constraint Handling
   Rules"); HDR §2.4, §2.5.1; src/builtin.elpi.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and
   be injected with the ``.. elpi::`` directive plus an ``:assert:`` line
   pinning the printed output.
