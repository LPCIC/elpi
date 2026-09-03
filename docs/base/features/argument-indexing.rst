##################
Argument indexing
##################

Indexing is a performance device: it prunes which rules are even attempted
against a goal, before matching runs for real. It never changes what a
program computes, only how fast rule selection finds the rules worth
trying.


The default and ``:index``
=============================

By default a predicate is indexed on its first argument, at depth 1 (the
argument's own head symbol, not looking inside it). ``:index (<spec>) "type"``
changes this, and is written before a ``pred`` / ``func`` signature
(:doc:`../syntax/type-declarations`):

.. code-block:: elpi

   :index (_ 1)
   pred mymap (A -> B), list A -> list B.

``<spec>`` is one number or ``_`` per argument, the depth to index that
argument at (``_`` means "don't index it", depth 0); ``(_ 1)`` indexes only
the second argument, one level deep. The optional string picks the technique:
``"Map"`` (a Patricia tree keyed on the head symbol, the default and the
only option when a single argument is indexed at depth 1), ``"Hash"``, or
``"DTree"``.

Changing the index never changes an answer. ``name-of`` here carries a
non-default ``:index`` and still computes the same result:

.. elpi:: ../code/indexing.elpi
   :assert: green


Which index to use
==================

The default costs almost nothing and fits almost every predicate. It looks at
one thing, the head symbol of the first argument, so it tells two rules
apart exactly when that symbol does. ``std.map``, ``std.mem`` and most
λProlog predicates have a few rules distinguished by precisely that, and the
index with the least overhead wins; :ref:`the HDR thesis <bib-hdr>` §3.2.5
reports that for the bulk of λProlog code the default beats the richer
indexes even where they would prune more.

A different index earns its keep when a predicate has *many* rules that the
first argument's head symbol does not separate. Two shapes bring that on: the
structure that distinguishes the rules sits deeper than depth 1 (or in a
later argument), or there are simply a great many rules, as in a ``copy`` or
``whd`` relation over a large object language, where scanning all of them on
every call is the cost that matters.

``"DTree"`` addresses the first. It walks the indexed arguments to their given
depth as a path through a shared trie, so a goal that disagrees with a rule
early in the path skips that rule together with every other rule that shares
the mismatched prefix. ``"Hash"`` addresses the second, cheaply and
approximately: a fixed-width bitmask per rule, AND-ed against the goal's, at
the price of the occasional collision that lets a doomed rule through.


Discrimination trees and hashes
==================================

Indexing more than one argument, or one argument deeper than 1, needs a
richer structure than a tree map. ``"DTree"`` linearizes the indexed
arguments, up to their given depth, into paths sharing a trie with every
other rule's paths; both the rule and the goal are walked the same way, so a
mismatched prefix prunes a whole subtree of rules at once.

``"Hash"`` instead reduces each indexed argument to a fixed-size bit pattern:
a rule contributes a ``1`` bit for what it can provide, a goal a ``1`` bit for
what it demands, and a rule is only attempted when every bit the goal demands
is also provided (the bitwise AND of the two hashes equals the goal's own
hash): a flexible goal demands nothing, a flexible rule provides everything.
Collisions can make the check imprecise, since the whole hash must fit one
machine word.

.. raw:: html

   <details class="elpi-fold"><summary>Hash indexing, worked out</summary>

Each indexed argument is reduced to a fixed-width string of bits, built
hierarchically down to that argument's indexing depth. A unification variable
in a rule head becomes a run of ``1``\ s; the same variable in a goal becomes
a run of ``0``\ s; a constant becomes a fixed mix of the two. A rule is tried
for a goal when ``hgoal & hrule`` equals ``hgoal``, that is, when the goal's
``1`` bits are a subset of the rule's.

The reading is: a ``1`` means "this piece of information is present". In a
rule it is *provided*, in a goal it is *required*. A flexible goal is all
``0``\ s and so requires nothing (``0 & x = 0``); a flexible rule is all
``1``\ s and so provides everything (``x & 1 = x``).

.. code-block:: elpi

   :index (2) "Hash"
   pred mult -> nat, nat, nat.
   mult o X o.
   mult (s (s o)) X C :- plus X X C.
   mult (s A) B C :- mult A B R, plus B R C.

``:index (2)`` indexes the first argument down to depth 2. Suppose the head
symbols hash as ``o = 1001 1011`` and ``s = 1011 0010`` (left-trimmed to one
machine word, eight bits here). The three rules' first arguments then hash to

.. code-block:: text

   1:  mult o          1001 1011
   2:  mult (s (s o))  0010 0010
   3:  mult (s A)      0010 1111     % A is a variable: 1s in its slot

and some goals select as follows (only the indexed first argument is shown),
keeping a rule when ``hgoal & hrule == hgoal``:

.. code-block:: text

   mult (s o) …    0010 1011    matches rule 3 only
   mult (s X) …    0010 0000    matches rules 2 and 3
   mult X …        0000 0000    matches every rule

.. raw:: html

   </details>
