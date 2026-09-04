##################
Argument indexing
##################

Indexing is a performance device: it prunes which rules are even attempted
against a goal, before matching runs for real. It never changes what a
program computes — only how fast rule selection finds the rules worth
trying.


The default and ``:index``
=============================

By default a predicate is indexed on its first argument, at depth 1 (the
argument's own head symbol, not looking inside it). ``:index (<spec>) "type"``
changes this — before a ``pred`` / ``func`` signature
(:doc:`../syntax/type-declarations`):

.. code-block:: elpi

   :index (_ 1)
   pred mymap i:(A -> B), i:list A, o:list B.

``<spec>`` is one number or ``_`` per argument, the depth to index that
argument at (``_`` means "don't index it" — depth 0); ``(_ 1)`` indexes only
the second argument, one level deep. The optional string picks the technique:
``"Map"`` (a binary search tree over head symbols — the default, and the only
option when a single argument is indexed at depth 1), ``"Hash"``, or
``"DTree"``.


Discrimination trees and hashes
==================================

Indexing more than one argument, or one argument deeper than 1, needs a
richer structure than a tree map. ``"DTree"`` linearizes the indexed
arguments, up to their given depth, into paths sharing a trie with every
other rule's paths — both the rule and the goal are walked the same way, so a
mismatched prefix prunes a whole subtree of rules at once.

``"Hash"`` instead reduces each indexed argument to a fixed-size bit pattern:
a rule contributes a ``1`` bit for what it can provide, a goal a ``1`` bit for
what it demands, and a rule is only attempted when every bit the goal demands
is also provided (the bitwise AND of the two hashes equals the goal's own
hash) — a flexible goal demands nothing, a flexible rule provides everything.
Collisions can make the check imprecise (the whole hash must fit one machine
word), but with more than one indexed argument it tends to prune better than
a discrimination tree at a similar cost.


Example
=======

.. elpi:: ../code/indexing.elpi
   :assert: green
