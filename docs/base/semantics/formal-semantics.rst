################
Formal semantics
################

A reference-level formalization of the previous three chapters: an abstract
syntax, the runtime objects the interpreter manipulates, and the big-step
rules that define how a query is run. It follows the
:ref:`HDR thesis <bib-hdr>` §2.5.1; the operational semantics of *dynamic*
predicates specifically (rules added and retracted while running, as
Rocq-Elpi does) is due to :ref:`Fissore & Tassi, PADL 2026 <bib-padl2026>`.
Read the previous three chapters first; this one names things rather than
motivating them.


Abstract syntax
================

.. math::

   \begin{array}{rll}
   p, q, f, g            & \in \mathrm{Pred}          & \text{functors (predicate / term constructors)} \\
   X, Y \ldots x, y       & \in \mathrm{Var}           & \text{unification variables, bound variables} \\
   \mathrm{App}          & ::= p\ \vec t \mid X\ \vec t & \text{applicative term} \\
   \mathrm{Atom}         & ::= \mathrm{cut} \mid \mathrm{delay}\ (\mathrm{App})\ \vec X \mid \mathrm{App} & \text{goal atom} \\
                         & \ \ \mid\ \mathtt{pi}\ x{\backslash}\ \mathrm{Atom} \mid \mathrm{Clause} \Rightarrow \mathrm{Atom} & \\
   \mathrm{Term}         & ::= \mathrm{App} \mid \lambda x.\ \mathrm{Term} & \text{term} \\
   \mathrm{Clause}       & ::= \mathrm{App} \mathrel{{:}{-}} \vec{\mathrm{Atom}} & \text{rule} \\
   \mathrm{Chr}          & ::= \vec{\mathrm{App}} \mathrel{\backslash} \vec{\mathrm{App}} \mid \mathrm{App} \Leftrightarrow \vec{\mathrm{App}} & \text{constraint rule}
   \end{array}

:math:`\mathrm{cut}` is the cut.
:math:`\mathrm{delay}\ c\ \vec X` is the abstract form of
:math:`\mathtt{declare\_constraint}`: it carries the applicative term
:math:`c` to suspend and the variables :math:`\vec X` that trigger its
resumption. A :math:`\mathrm{Chr}` rule is a list of patterns to match, a
list of patterns to match *and remove*, a guard (defaulting to "always true"
in the concrete syntax) and a list of new goals; its concrete-syntax spelling
is described in :doc:`../syntax/constraint-handling-rules`.


Runtime objects
================

A *substitution* :math:`\sigma` is a partial map from unification variables
to terms; :math:`\sigma\ t` applies it to :math:`t`, and
:math:`\mathrm{dom}(\sigma)` is the set of variables it assigns. Two functions
extend a substitution:

.. math::

   \begin{aligned}
   \mathrm{unify} &: \mathrm{Term} \times \mathrm{Term} \times \Sigma \rightharpoonup \Sigma \\
   \mathrm{match}  &: \mathrm{Term} \times \mathrm{Term} \times \Sigma \rightharpoonup \Sigma
   \end{aligned}

:math:`\mathrm{unify}(t_1, t_2, \sigma) = \sigma'` is the most general
extension of :math:`\sigma` such that :math:`\sigma' t_1 = \sigma' t_2`
(:ref:`Miller, 1992 <bib-miller92>`).
:math:`\mathrm{match}(t, p, \sigma) = \sigma'` is the most general extension of
:math:`\sigma` such that :math:`\sigma' p = \sigma t`; it only ever assigns
variables of the *pattern* :math:`p`, never ones already in :math:`t`, and this is
what makes a signature's input arguments matched rather than unified
(:doc:`constraints`). Both are partial: on failure they return :math:`\bot`.

A *program* :math:`\pi = (N, I)` pairs a set of names :math:`N` (the
constants introduced by :math:`\mathtt{pi}`) with an index :math:`I` mapping
each predicate to an *ordered* list of rules. :math:`h + \pi` prepends the
rules :math:`h` to that index, giving them top priority; this is how
:math:`{\Rightarrow}` extends the program for one goal.

A *constraint store* :math:`\kappa` is a *multiset* of triples
:math:`(\pi, c, t)`: a program, a constraint (an applicative term), and a
trigger (a list of variables). The store's semantics is covered in detail in
:doc:`chr`.

A *goal* is a triple :math:`(\pi, \mathrm{atom}, a)`: the program to solve
the atom against, and the list of *cut-to* *alternatives*, what
:math:`\mathrm{cut}` restores. An alternative is itself a triple
:math:`(\kappa, \sigma, gs)`: a constraint store, a substitution, and the
list of goals still to solve along that branch.


The semantics
=============

.. math::

   \mathrm{run} : \mathrm{Alt} \times [\mathrm{Alt}] \to (K \times \Sigma \times [\mathrm{Alt}]) \uplus \{\bot\}

:math:`\mathrm{run}` takes the current alternative (its pending goals, store
and substitution) and the list of alternatives still available, and either
returns an updated store, substitution and remaining alternatives, or
:math:`\bot` when every alternative has been exhausted. We write a
*configuration* :math:`\langle gs \mid a \mid \sigma \mid \kappa\rangle` for
one pending goal list together with the rest of that state, and
:math:`\longrightarrow` for one step of :math:`\mathrm{run}`; repeating
:math:`\longrightarrow` until it gets stuck at :math:`\mathrm{stop}` or
:math:`\mathrm{abort}` below is what :math:`\mathrm{run}` computes. To keep
the rules narrow we write a goal at the head of :math:`gs` as its program
paired with its atom, :math:`(\pi, \mathrm{atom})`, eliding the goal's own
cut-to alternatives except in :math:`\mathrm{cut}`, the one rule that reads
them.

The rules that touch the constraint store (:math:`\mathrm{delay}`,
:math:`\mathrm{resume}`) take priority and are tried first; the rest are
syntax-directed on the goal at the head of :math:`gs`. The
:math:`\mathrm{resume}` rule follows :ref:`Michaylov & Pfenning, 1993
<bib-michaylov>`, which reads a higher-order logic programming language as a
constraint logic programming one.

:math:`\mathrm{stop}`
   .. math::

      \dfrac{}{\langle [\,] \mid a \mid \sigma \mid \kappa\rangle\ \to\ (\kappa,\ \sigma,\ a)}

   an empty goal list returns the current store, substitution and
   alternatives.

:math:`\mathrm{call}` (and :math:`\mathrm{backtrack}`, :math:`\mathrm{abort}`)
   :math:`\mathrm{backchain}` (below) produces one alternative per rule that
   applies to the goal at the head of :math:`gs`:

   .. math::

      \dfrac{\mathrm{backchain}(\kappa, \pi, p\,\vec t, gs, \sigma, a) = (\kappa, \sigma_1, gs_1) :: rest}
            {\langle (\pi, p\,\vec t) :: gs \mid a \mid \sigma \mid \kappa\rangle \longrightarrow \langle gs_1 \mid rest \mathbin{+\!+} a \mid \sigma_1 \mid \kappa\rangle}

   the first alternative becomes the new configuration, its own leftover
   rules :math:`rest` pushed in front of :math:`a`. If
   :math:`\mathrm{backchain}` is empty and :math:`a = a_0 :: a_s`, pop
   :math:`a_0` instead, *chronological backtracking* to the most recent
   choice point, undoing every assignment made since. If it is empty and
   :math:`a = [\,]`, the whole computation aborts: :math:`\bot`.

:math:`\mathrm{cut}`
   .. math::

      \dfrac{}{\langle (\pi, \mathrm{cut}, a_{cut}) :: gs \mid a \mid \sigma \mid \kappa\rangle
              \longrightarrow
              \langle gs \mid a_{cut} \mid \sigma \mid \kappa\rangle}

   :math:`\mathrm{cut}` at the head of the goal list discards every alternative created
   since the enclosing rule was selected, by replacing the current
   alternatives :math:`a` with the goal's own cut-to alternatives
   :math:`a_{cut}`; the :math:`\mathrm{cut}` goal is the one place a goal's third
   component is read. This is why the cut is *hard*: alternatives left over
   from premises solved earlier in the same rule are discarded too, not only
   the untried rules for the predicate.

:math:`\beta`
   .. math::

      \dfrac{\sigma\,(X\,\vec t) \;=_{\beta\eta}\; p\,\vec u}
            {\langle (\pi, X\,\vec t) :: gs \mid a \mid \sigma \mid \kappa\rangle
             \longrightarrow
             \langle (\pi, p\,\vec u) :: gs \mid a \mid \sigma \mid \kappa\rangle}

   if the head of the goal is a unification variable and :math:`\sigma X`
   applied to :math:`\vec t` :math:`\beta`/:math:`\eta`-reduces to an
   applicative term :math:`p\,\vec u`, the goal is replaced by it. This is
   what lets a unification variable stand for a predicate, as in
   :math:`P = \mathtt{true},\ P`.

:math:`\mathtt{pi}`
   .. math::

      \dfrac{y \mathbin{\#} \pi}
            {\langle (\pi, \mathtt{pi}\ x{\backslash}\ g) :: gs \mid a \mid \sigma \mid \kappa\rangle
             \longrightarrow
             \langle (y{+}\pi, g[x/y]) :: gs \mid a \mid \sigma \mid \kappa\rangle}

   :math:`\mathtt{pi}\ x{\backslash}\ g` picks a name :math:`y` fresh for the
   program (:math:`y \mathbin{\#} \pi`, HDR's notation for "fresh in"), adds
   it to :math:`\pi`, and continues with :math:`g[x/y]`, the body with the
   fresh name put in for the bound variable.

:math:`{\Rightarrow}`
   .. math::

      \dfrac{}{\langle (\pi, h \Rightarrow g) :: gs \mid a \mid \sigma \mid \kappa\rangle
              \longrightarrow
              \langle (h{+}\pi, g) :: gs \mid a \mid \sigma \mid \kappa\rangle}

   :math:`h \Rightarrow g` continues with :math:`g` under :math:`h + \pi`:
   the extra rules :math:`h` prepended to the program, for the duration of
   :math:`g` only.

:math:`\mathrm{delay}`
   :math:`\mathrm{delay}\ c\ \vec X`, the abstract form of
   :math:`\mathtt{declare\_constraint}`, adds :math:`(\pi, c, \vec X)` to
   the store. Because a new constraint may
   immediately enable a constraint handling rule, :math:`\mathcal{CHR}`
   (below) runs right away; whatever goals it produces are solved *before*
   the rest of the current branch:

   .. math::

      \dfrac{\mathcal{CHR}(\kappa, \pi, c, \vec X, a) = (gs', \kappa')}
            {\langle (\pi, \mathrm{delay}\ c\ \vec X) :: gs \mid a \mid \sigma \mid \kappa\rangle \longrightarrow \langle gs' \mathbin{+\!+} gs \mid a \mid \sigma \mid \kappa'\rangle}

:math:`\mathrm{resume}`
   whenever the store holds a constraint :math:`(\pi, c, t)` some variable of
   which is now in :math:`\mathrm{dom}(\sigma)`, it is removed from the store
   and :math:`c` is solved next, ahead of every pending goal, under program
   :math:`\pi` and the current alternatives as its cut-to list (irrelevant
   there, since :math:`c` is an applicative term, never :math:`\mathrm{cut}`):

   .. math::

      \dfrac{(\pi, c, t) \in \kappa \quad \exists X \in t,\ X \in \mathrm{dom}(\sigma)}
            {\langle gs \mid a \mid \sigma \mid \kappa\rangle \longrightarrow \langle (\pi, c) :: gs \mid a \mid \sigma \mid \kappa - (\pi, c, t)\rangle}


Backchain
+++++++++++++

:math:`\mathrm{backchain}` builds one alternative per rule of :math:`p` that
applies to the goal :math:`p \vec t`:

.. math::

   \begin{aligned}
   \mathrm{backchain}(\kappa, \pi, p\,\vec t, gs, \sigma, a)\ = \Big[\ &(\kappa,\ \sigma',\ [(\pi, g, a) \mid g \in \vec b] \mathbin{+\!+} gs) \\
     \text{for}\ &(p\ \vec u \mathrel{{:}{-}} \vec b) \in \pi\ p \\
     \text{if}\ &\mathrm{select}({\vec t\ \vec u},\, \sigma) = \sigma' \neq \bot\ \Big]
   \end{aligned}

in the order the rules appear in :math:`\pi\ p`. Every new goal of every
alternative carries the *same* cut-to list :math:`a`, the alternatives that
existed right before backchaining, not any created by it or by exploring its
results.


Select
++++++++

:math:`\mathrm{select}` is what makes a signature's inputs matched and its
outputs unified: given the pairs of a rule's head arguments with the goal's,
it folds :math:`\mathrm{match}` over the input pairs and :math:`\mathrm{unify}`
over the output pairs:

.. math::

   \begin{aligned}
   \mathrm{select}({\vec t\ \vec u},\, \sigma) =\ &\mathrm{fold}\ \mathrm{unify}\ {\vec t\ \vec u}_{\,\mathrm{out}} \\
     &\ \big(\mathrm{fold}\ \mathrm{match}\ {\vec t\ \vec u}_{\,\mathrm{in}}\ \sigma\big)
   \end{aligned}

folding :math:`\bot` through either step aborts the whole rule, as does a
failed :math:`\mathrm{match}` or :math:`\mathrm{unify}` on any one pair.


The :math:`\mathcal{CHR}` procedure
++++++++++++++++++++++++++++++++++++

A constraint rule :math:`G_1 \mathrel{\backslash} G_2 \mid T \Leftrightarrow G_3`
has a logical reading, :math:`T \land G_1 \Rightarrow (G_2 \Leftrightarrow G_3)`:
when the guard :math:`T` holds, :math:`G_2` may be replaced by :math:`G_3`,
provided :math:`G_1` still needs to be solved. :math:`\mathcal{CHR}` computes
this for one freshly declared or resumed constraint, the *active*
constraint, following the *refined operational semantics* of
:ref:`Duck, Stuckey, García de la Banda & Holzbaur, 2004 <bib-chr2004>`, as
formalized by :ref:`Guidi, Sacerdoti Coen & Tassi, 2019 <bib-tassi2019>`
(:doc:`chr` gives the informal, 8-step version of exactly this procedure):

.. math::

   \mathcal{CHR}(\kappa, \pi, c, t, a) = (g', \kappa')\ \text{where}

1. the active constraint :math:`(\pi, c, t)` is added to :math:`\kappa` to get
   :math:`\kappa'`, and :math:`g'` starts empty;
2. for each rule :math:`P_1 \ldots P_x \mathrel{\backslash} P_{x+1} \ldots P_n \mid Q \Leftrightarrow G`
   of the active constraint's clique, in declaration order;
3. for each position :math:`0 < j \le n`, in increasing order;
4. for each permutation :math:`C_1 \ldots C_n` of constraints in
   :math:`\kappa'` with :math:`C_j = (\pi, c, t)`;
5. match every :math:`C_i` against :math:`P_i`, and run the guard :math:`Q` in
   the program the top-level query was launched against, not in the :math:`\pi`
   carried by any matched constraint (:ref:`HDR <bib-hdr>` §2.5.1);
   on success, committing to this rule, this position and this permutation,
   remove :math:`C_{x+1} \ldots C_n` from :math:`\kappa'`, discard every
   remaining permutation that mentions any of them, and add the (substituted)
   :math:`G` to :math:`g'`;
6. continue with the next rule at step 2.

Two refinements make this tractable. First, unless a constraint's trigger is
the shared wildcard that opts it out (:doc:`chr`), step 4 only considers
permutations whose constraints have a trigger overlapping :math:`t`,
clustering the store instead of considering every constraint against every
other one. Second, step 1
actually freshens :math:`(\pi, c, t)`'s own names before adding it, so that
the names of every constraint in the store stay pairwise disjoint; this is
the "frozen into its own space of names" of :doc:`chr`.
