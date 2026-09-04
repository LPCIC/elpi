####################
Elpi = λProlog + CHR
####################

Elpi runs a query by building a **proof tree**, depth-first: a rule becomes a
node whose branching factor is its number of premises. At any point one open
branch is *active* — its tip is the goal currently being worked on — and
every other open branch is *inert*. Four actions drive the construction:

1. **run** — solve the active goal against the program: pick a rule whose
   head unifies with it (:doc:`../syntax/inference-rules-and-queries`), and
   continue with its premises, or with an inert branch promoted to active;
2. **suspend** — instead of solving the active goal, turn it into a
   **constraint** kept in the *constraint store*, recording which variables
   should wake it up (:doc:`../syntax/constraint-handling-rules`); the branch
   pauses, and an inert branch is promoted to active in its place;
3. **resume** — when one of those variables is assigned, by ``run`` acting
   elsewhere in the tree, the constraint is turned back into an active goal
   and its branch continues;
4. **handle** — after each of the above, a **constraint handling rule** may
   fire over *all* suspended branches at once. It can drop a constraint,
   pruning its branch for good, or add a fresh goal, starting a new one.

``run``, ``suspend`` and ``resume`` build an ordinary — if pausable — proof
tree, one branch at a time. ``handle`` is different in kind: it is a step
over the *whole* set of suspended branches, so it can do things no
single-branch step can, such as noticing that two suspended goals contradict
each other and replacing both with ``false``, or merging two identical
branches into one (in effect building a DAG, not just a tree, of the proof
search).

.. figure:: /_static/chr.png
   :alt: A proof tree under construction, with an active goal, inert goals, a
         branch suspended into a constraint, and a constraint handling rule
         connecting two suspended branches.
   :width: 70%
   :align: center

   The four actions on an Elpi computation — run (1), suspend (2), resume (3),
   handle (4) — from the author's HDR thesis.

This part of the manual follows that split:
:doc:`logic-programming-model` covers ``run`` — Elpi as Prolog, and as
λProlog with binders; :doc:`constraints` covers ``suspend`` and ``resume`` —
why an incomplete term needs them and what a constraint is; :doc:`chr` covers
``handle`` — the constraint store and constraint handling rules in detail;
:doc:`formal-semantics` gives the reference-level formalization of all four.


Example
=======

.. elpi:: ../code/four-actions.elpi
   :assert: suspend\nsuspend\nhandle: drop a duplicate\nresuming, Y = 4\nrun: recurse\nrun: recurse\nrun: base case\ndone
