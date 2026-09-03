####################
Elpi = λProlog + CHR
####################

Elpi runs a query by building a **proof tree**, depth-first: a rule becomes a
node whose branching factor is its number of premises. At any point one open
branch is *active*, its tip the goal currently being worked on, and every
other open branch is *inert*. Four actions drive the construction:

1. **run**: solve the active goal against the program. Pick a rule whose head
   unifies with it (:doc:`../syntax/inference-rules-and-queries`) and continue
   with its first premise; when a branch closes, the next open goal in the
   depth-first walk becomes active;
2. **suspend**: instead of solving the active goal, turn it into a
   **constraint** kept in the *constraint store*, recording which variables
   should wake it up (:doc:`../syntax/constraint-handling-rules`). The branch
   pauses and the search moves to that same next open goal: in ``p :- a, b``
   with ``a`` suspended, ``b`` is worked on next;
3. **resume**: when one of those variables is assigned, by ``run`` acting
   elsewhere in the tree, the constraint is turned back into an active goal
   and its branch continues;
4. **handle**: after each of the above, a **constraint handling rule** may
   fire over *all* suspended branches at once. It can drop a constraint,
   pruning its branch for good, or add a fresh goal, starting a new one.

``run``, ``suspend`` and ``resume`` build an ordinary, if pausable, proof
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

   The four actions on an Elpi computation, run (1), suspend (2), resume (3)
   and handle (4), from the author's :ref:`HDR thesis <bib-hdr>`.

This part of the manual follows that split. ``run`` is covered in
:doc:`logic-programming-model`: Elpi as Prolog, and as λProlog with binders.
``suspend`` and ``resume`` are covered in :doc:`constraints`: why an
incomplete term needs them and what a constraint is. ``handle`` is covered in
:doc:`chr`: the constraint store and constraint handling rules in detail. A
reference-level formalization of all four is given in :doc:`formal-semantics`.

A single goal exercises all four: it runs, suspends twice on an unknown ``Y``,
has a constraint handling rule drop one of the duplicates, then resumes and
runs to completion once ``Y`` is filled in.

.. elpi:: ../code/four-actions.elpi
   :assert: suspend\nsuspend\nhandle: drop a duplicate\nresuming, Y = 4\nrun: recurse\nrun: recurse\nrun: base case\ndone
