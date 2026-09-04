##############################
Hindley-Milner type inference
##############################

Algorithm W infers a type for every expression without type annotations,
and — the part that makes it a good showcase for Elpi — turns some inferred
types into **schemes**, universally quantified over the type variables used
*only* locally: ``let id = λx.x in (id one, id empty)`` has to accept ``id``
at two different types.

.. elpi:: ../code/hindley-milner.elpi
   :assert: well typed, of type mono integer

A monotype is a type with no quantifiers — an arrow ``===>``, an applied type
constructor ``#`` (as in ``list # integer``), or a type variable, itself an
ordinary Elpi unification variable, an existential hole
(:doc:`../semantics/constraints`). A **scheme** is ``mono T`` (no
quantification) or ``all F``, universally quantifying one more variable and
continuing as ``F`` applied to it. ``specialize`` goes the other way: given a
scheme, it produces one monotype by picking a *fresh* unification variable
for every ``all`` — the same mechanism ``pi`` uses for a fresh bound name,
here applied to open a scheme's quantifiers into fresh holes to be filled in
by whatever unifies with them at this particular use.

The interesting rule is ``let``:

.. code-block:: elpi

   w (let F FP B) (mono TC) :-
     w F (mono FT),
     declare_constraint (overbar (mono FT) FP) [],
     pi x\ w x FP ==> w (B x) (mono TC).

``FP`` — the scheme eventually given to the let-bound name — is not computed
on the spot. Generalizing ``FT`` means comparing its free type variables
against the free type variables of Γ, the *set of hypothetical* ``w`` *rules
currently in scope*: exactly the ``==>`` rules nested ``pi``/``let``s have
added so far. Γ is not a first-class value an ordinary goal can inspect —
this is beyond what ``pi``/``==>`` alone can do
(:doc:`../semantics/logic-programming-model`). A constraint handling rule
can: its sequent pattern ``(G ?- goal)`` binds ``G`` to the very context a
suspended goal carries with it (:doc:`../syntax/constraint-handling-rules`,
:doc:`../semantics/chr`). So generalization is written as a suspended
``overbar`` constraint, resolved by one CHR rule once the goal it is attached
to is later matched:

.. code-block:: elpi

   constraint w overbar {
     rule \ (G ?- overbar T T1)
          | (generalize G T POLYT) <=> (T1 = POLYT).
   }

``generalize`` collects the free variables of the monotype and of Γ, and
quantifies exactly those that are free in the former but not the latter — the
ones the surrounding context makes no assumption about.

This covers the core of the algorithm; the full version in
``tests/sources/w.elpi`` this example is adapted from, and the richer
``tests/sources/toyml/`` (equality-type variables — Standard ML's ``''a`` —
and a bidirectional variant that propagates a known result type inward
instead of only inferring one outward), are further reading for anyone
implementing a real ML-style checker in Elpi.
