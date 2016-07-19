(*
  Propositions as Types
*)

include "basics/logic.ma".

(* In the previous section, we introduced many interesting logical connectives 
by means of inductive definitions in the sort Prop. Do the same constructions 
make any sense in Type? The answer is yes! Not only they make sense, but they 
are indeed very familiar constructions: cartesian product, disjoint sum, empty 
and singleton types, and ``sigma types'' (disjoint union of families of types 
indexed over a given base type). This is not a coincidence, but a consequence of 
a strong principle known under the name of ``Propositions as Types analogy'' (or 
Curry-Howard correspondence).

We shall first discuss the constructions, and then we shall come back on the 
general analogy.*)

(***************************** Cartesian Product ******************************)

(* The cartesian product of two types A and B is defined as follows: *)

inductive Prod (A,B:Type[0]) : Type[0] ≝
  pair : A → B → Prod A B.
  
(* Observe that the definition is identical to the definition of the logical 
conjunction, but for the fact that the sort Prop has been replaced by Type[0].

The following declarations allows us to use the canonical notations A × B for 
the product and 〈a,b〉 for the pair of the two elements a and b. *)

notation "hvbox(x break × y)" with precedence 70 for @{ 'product $x $y}.
interpretation "Cartesian product" 'product A B = (Prod A B).

notation "hvbox(\langle term 19 a, break term 19 b\rangle)" 
  with precedence 90 for @{ 'pair $a $b}.
interpretation "Pair construction" 'pair x y = (pair ?? x y).

(* We can define the two projections fst and snd by a simple case analysis of 
the term: *)

definition fst ≝ λA,B.λp:A×B. match p with [pair a b ⇒ a].
definition snd ≝ λA,B.λp:A×B. match p with [pair a b ⇒ b].

(* As in the case of inductive propositions, Matita automatically generates
elimination principles for A × B. In this case, however, it becomes interesting
to consider the possibility that the proposition towards which we are 
eliminating a given pair p:A × B$ contains a copy of p itself. In other words, 
if we have p:A × B in the current context, it is possible that p also occurs in 
the current goal, that is that the current goal "depends" on p.

A typical example is in the proof of the so called ``surjective pairing'' 
property: *)

lemma surjective_pair: ∀A,B.∀p:A×B. p = 〈fst ?? p, snd ?? p〉.

(* where p explicitly occurs in the conclusion. The proof is straightforward: we 
introduce A, B and p and proceed by cases on p: since p is a pair, the only 
possible case is that it is of the form 〈a,b〉 for some a and b.*)

#A #B #p cases p #a #b

(* At this point the goal looks like 
      〈a,b〉 = 〈fst A B  〈a,b〉, snd A B 〈a,b〉〉 
and the two sides of the equation are convertible. *)
// qed.

(* When we call cases p we are actually applying the dependent elimination 
principle Prod_ind for the product, so it becomes interesting to have a look at 
it (we shall postpone the discussion of the way it is generated in a later 
section):

  ∀A,B.∀P:A×B →Prop.(∀a:A,∀b:B. P 〈a,b〉) → ∀x:A×B.P x
  
The previous principle has a very natural backward reading: in order to prove 
that the property (P x) holds for any x of type A×B it is enough to prove P〈a,b〉 
for any a:A and b:B. *)

(******************************* Disjoint Sum *********************************)

(* By reflecting in Type the definition of the logical disjunction we obtain the 
disjoint union (the sum) of two types: *)

inductive Sum (A,B:Type[0]) : Type[0] ≝
  inl : A → Sum A B
| inr : B → Sum A B.

notation "hvbox(a break + b)" 
  left associative with precedence 55 for @{ 'plus $a $b }.

interpretation "Disjoint union" 'plus A B = (Sum A B).

(* The two constructors are the left and right injections. The dependent 
elimination principle Sum_ind has the following shape: 

  ∀A,B.∀P:A+B →Prop.
    (∀a:A.P (inl A B a)) → (∀b:B.P (inr A B b))  → ∀x:A×B.P x
    
that is, in order to prove the property (P x) for any x:A+B it is enough to
prove P (inl A B a) and P (inr A B b) for all a:A and b:B. *)

(************************* Empty Type and Unit Type ***************************)

(* The counterparts of False and True are, respectively, an empty type and a 
singleton type: *)

inductive void : Type[0] ≝.
inductive unit : Type[0] ≝ it: unit.

(* The elimination principle void_ind for void is simply 

     ∀P:void→Prop.∀x:void.P x
   
stating that any property is true for an element of type void (since we have no
such element).

Similarly, the elimination principle for the unit type is:

    ∀P:unit→Prop. P it → ∀x:unit.P x
  
Indeed, in order to prove that a property is true for any element of the unit
type, it is enough to prove it for the unique (canonical) inhabitant "it".

As an exercise, let us prove that all inhabitants of unit are equal to each 
other: *)

lemma eq_unit: ∀a,b:unit. a = b.

(* The idea is to proceed by cases on a and b: we have only one possibility, 
namely a=it and b=it, hence we end up to prove it=it, that is trivial. Here is 
the proof: *) 

#a cases a #b cases b // qed. (* also: * * // qed. *)

(* It is interesting to observe that we get exactly the same behavior by 
directly applying unit_ind instead of proceeding by cases. In fact, this is an 
alternative proof: *)

lemma eq_unit_again: ∀a,b:unit. a = b.
@unit_ind @unit_ind // qed.

(********************* Sigma Types and dependent matching *********************)

(* As a final example, let us consider ``type'' variants of the existential 
quantifier; in this case we have two interesting possibilities: *)

inductive Sig (A:Type[0]) (Q:A → Prop) : Type[0] ≝
   Sig_intro: ∀x:A. Q x →  Sig A Q.

inductive DPair (A:Type[0]) (Q:A → Type[0]) : Type[0] ≝
   DPair_intro: ∀x:A. Q x →  DPair A Q.

(* We shall use the notation Σx:A.Q x for the sigma type, and the similar 
notation ∑x:A.Q x for dependent pairs. *)

notation "hvbox(\Sigma ident i : ty break . p)"
 left associative with precedence 20 
for @{'sigma (\lambda ${ident i} : $ty. $p) }.

notation "hvbox(\Sigma ident i break . p)"
 with precedence 20 for @{'sigma (\lambda ${ident i}. $p) }.
 
interpretation "Sigma" 'sigma x = (Sig ? x).

notation "hvbox(∑ ident i : ty break . p)"
 left associative with precedence 20 
 for @{'dpair (\lambda ${ident i} : $ty. $p) }.

notation "hvbox(∑ ident i break . p)" 
 with precedence 20 for @{'dpair (\lambda ${ident i}. $p) }.
 
interpretation "Sum" 'dpair x = (DPair ? x).

(* In the first case (traditionally called sigma type), an element of type 
(Sig A P) is a pair (Sig_intro ?? a h) where a is an element of type A and h is a 
proof that the property (P a) holds. 

A suggestive reading of (Sig A P) is as the subset of A enjoying the property P, 
that is {a:A | P(a)}.

In the second case, an element of DPair A B is a "dependent" pair 
(DPair_intro ?? a h) where a is element of type A and h maps a into an element in 
(B a); the intuition is to look at DProd A B as a (disjoint) family of sets B_a 
indexed over elements a:A. 

In both case it is possible to define projections extracting the two components
of the pair. Let us discuss the case of the sigma type (the other one is 
analogous). 

Extracting the first component (the element) is easy: *)

definition Sig_fst  ≝ λA:Type[0].λP:A→Prop.λx:Sig A P. 
  match x with [Sig_intro a h ⇒ a].

(* Getting the second component is a bit trickier. The first problem is
the type of the result: given a pair (Sig_intro ?? a h): Sig A P, the type of 
h is (P a), that is P applied to the first argument of the pair of which we want 
to extract the second component! 
Luckily, in a language with dependent types, it is not a problem to write such a
a type: 

  definition Sig_snd : ∀A,P.∀x:Sig A P.P (Sig_fst A P x) ≝ ...

A subtler problem is met when we define the body. If we just write 

  definition Sig_snd : ∀A,P.∀x.Sig A P → P (Sig_fst A P x) ≝ λA,P,x.
    match x with [Sig_intro a h ⇒ h].

the system will complain about the type of h. The point is that the type of this 
term depends on a, that is, in a not so trivial way, from the input argument x. 
In this situations, the type inference algorithm of Matita requires a little 
help: in particular the user is asked to explicitly provide the return type of 
the match expression, that is a map uniformly expressing the type of all 
branches of the case as a function of the matched expression. 
In our case we only have one branch and the return type is  

   λx.P (Sig\_fst A P x)

We declare such a type immediately after the match, introduces by the keyword 
``return'': *)

definition Sig_snd : ∀A,P.∀x:Sig A P.P (Sig_fst A P x) ≝ λA,P,x.
  match x return λx.P (Sig_fst A P x) with [Sig_intro a h ⇒ h].
  
(* Similarly, we have: *)

definition DPair_fst  ≝ λA:Type[0].λP:A→Type[0].λx:DPair A P. 
  match x with [DPair_intro a h ⇒ a].
  
definition DPair_snd : ∀A,P.∀x:DPair A P.P (DPair_fst A P x) ≝ λA,P,x.
  match x return λx.P (DPair_fst A P x) with [DPair_intro a h ⇒ h].
  
(* Remark: The careful reader may have possibly remarked that we also did a 
systematic abuse of the arrow symbol: the expression A → B was sometimes 
interpreted as the "implication" between A and B and sometimes as the "function 
space" between A and B. The reason of this fact is that, actually, in a 
foundational system like the Calculus of Construction, they are the very same 
notion: we only distinguish them according to the sort of the resulting 
expression.
Similarly for the dependent product ∏x:A.B: if the resulting expression is of 
sort Prop we shall look at it as a "universal quantification" (using the 
notation ∀x:A.B), while if it is in Type we shall typically regard it as a 
generalized cartesian product of a family of types B indexed over a base type A.
*)

(************************ Kolmogorov interpretation ***************************)

(* The previous analogy between propositions and types is a consequence of a 
deep philosophical interpretation of the notion of proof in terms of a 
constructive procedure that transforms proofs of the premises into a proof of 
the conclusion. This usually referred to as Kolmogorov interpretation, or 
Brouwer–Heyting–Kolmogorov (BHK) interpretation.

The interpretation states what is intended to be a proof of a given formula φ, 
and is specified by induction on the structure of A:

- a proof of P∧Q is a pair 〈a,b〉 where a is a proof of P and b is a proof of Q;
- a proof of P∨Q is a pair 〈a,b〉 where either a is 0 and b is a proof of P, or 
  a=1 and b is a proof of Q; 
- a proof of P→Q is a function f which transforms a proof of x:P into a proof of 
  (f x):Q;
- a proof of ∃x:S.φ(x) is a pair 〈a,b〉 where a is an element of S, and b is a 
  proof of φ(a);
- a proof of ∀x:S.ϕ(x) is a function f which transforms an element x of S into a 
  proof of \varphi(a);
- the formula ¬P is defined as P → False, so a proof of it is a function f which 
  transforms a proof of P into a proof of False;
- there is no proof of False.

For instance, a proof of the formula P → P is a function transforming a proof of 
P into a proof of P: but we can just take the identity!

You can explicitly exploit this idea for writing proofs in Matita. Instead of 
declaring a lemma and proving it interactively, you may define your lemma as if 
it was the type of an expression, and directly proceed to inhabit it with its 
proof: *)

definition trivial: ∀P:Prop.P→P ≝ λP,h.h.

(* It is interesting to observe that this is really the very same proof
(intensionally!!) that would be produce interactively, as testified by the 
following fragment of code: *)

lemma trivial1: ∀P:Prop.P→P. #P #h @h qed.
lemma same_proofs: trivial = trivial1. @refl qed.

(* Even more interestingly, we can do the opposite, namely define functions
interactively. 
Suppose for instance that we need to define a function with the following
type: ∀A,B,C:Type[0]. (A → B → C) → A× B → C.
If we just declare the type of the function followed by a fullstop, Matita will 
start an interactive session completely analogous to a proof session, and we can 
use the usual tactics to ``close the goal'', that is to inhabit the type. *)

definition uncurrying: ∀A,B,C:Type[0]. (A→B→C)→A×B→C.
#A #B #C #f * @f qed.

(********************** The Curry-Howard correspondence ***********************)

(* The philosophical ideas contained in the BHK interpretation of a proof as a
constructive procedure building a proof of the conclusion from proofs of the 
hypothesis get a precise syntactical systematization via the so called 
Curry-Howard correspondence, expressing a direct relationship between computer 
programs and proofs. 
The Curry-Howard correspondence, also known as proofs-as-programs analogy, is a 
generalization of a syntactic analogy between systems of formal logic and 
computational calculi first observed by Curry for Combinatory Logic and Hilbert-
style deduction systems, and later by Howard for λ-calculus and Natural 
Deduction: in both cases the formation rules for well typed terms have precisely 
the same shape of the logical rules of introduction of the correspondent 
connective.
 
As a consequence, the expression 

        M:A
        
really has a double possible reading: 

- M is a term of type A
- M is a proof of the proposition A

In both cases, M is a witness that the object A is "inhabited". A free variable 
x:A is an assumption about the validity of A (we assumeto have an unknown proof 
named x). Let us consider the cases of the introduction and elimination rule of 
the implication in natural deduction, that are particularly interesting:

      Γ,A ⊢ B                    Γ ⊢ A → B    Γ ⊢ A
      ----------                 -------------------
      Γ ⊢ A → B                         Γ ⊢ B
     
The first step is to enrich the representation by decorating formulae with
explicit proof terms. In particular, formulae in the context, being assumptions,
will be decorated with free variables (different form each others), while the 
conclusion will be decorated with a term expression with free variables 
appearing in the context.

Suppose Γ,x:A ⊢ M:B. What is the expected decoration for A → B?
According to Kolmogorov interpretation, M is a procedure transforming the proof 
x:A into a proof of M:B; the proof of A → B is hence the function that, taken x 
as input, returns M, and our canonical notation for expressing such a function 
is λx:A.M. Hence we get:

    Γ,x:A ⊢ M:B
    -----------------
    Γ ⊢ λx:A.M: A → B
    
that is precisely the typing rule for functions. 

Similarly, let us suppose that Γ ⊢ M:A → B,  and Γ ⊢ N:A, and let us derive a 
natural proof decoration for the arrow elimination rule (that is just the well 
known modus ponens rule). Again, we get inspiration from Kolmogorov 
interpretation: a proof M:A → B is a function transforming a proof of A into a 
proof of B hence, since we have a proof N:A in order to get a proof of B it is 
enough to apply M to the argument N:

    Γ ⊢ M: A → B      Γ ⊢ N: A 
    --------------------------
          Γ ⊢ (M N):B 
          
But this is nothing else than the typing rule for the application!

There is still a point that deserve discussion: the most interesting point of p
rograms is that they can be executed (in a functional setting, terms can be 
reduced to a normal form). By the Curry-Howard correspondence, this should 
correspond to a normalization procedure over proofs: does this operation make 
any sense at the logical level? Again the answer is yes: not only it makes 
sense, but it was independently investigated in the field of proof theory. A 
reducible expression corresponds to what is traditionally called a "cut". A cut
is a logical ``detour'' typically arising by an introduction rule immediately 
followed by an elimination rule for the same connective, as in a beta-redex, where 
we have a direct "interaction" between an application and a λ-abstraction:

    (beta-rule)   λx.M N → M[N/x] 
    
One of the main meta-theoretical results that is usually investigated on proof 
systems is if they enjoy the so called "cut-elimination" principle, that is if 
the cut-rule is "admissible": any proof that makes use of cuts can be turned 
into a cut-free proof. Since a cut is redex, a cut-free proof is a term that 
does not contain any redex, that is a term in normal form.
Hence, the system enjoys cut-elimination if and only if the corresponding 
calculus is normalizing.

Cut-elimination is a major tool of proof theory, with important implications on
e.g. "consistency", "automation" and "interpolation". 

Let us make a final remark. If a program is a proof, then what does it 
correspond to the act of verifying the correctness of a proof M of some 
proposition A? Well, M is just an expression that is supposed to have type A, so 
"proof verification" is nothing else that "type checking"! 

This should also clarify that proof verification is a much easier task than 
proof search. While the former corresponds to type checking, the second
one corresponds to the automatic synthesis of a program from a specification!

The main ideas behind the Curry-Howard correspondence are summarized in the 
following Picture:

               Curry-Howard Correspondence

          Logic           | Programming
                          |
          proposition     | type
          proof           | program 
          cut             | reducible expression (redex) 
          cut free        | normal form 
          cut elimination | normalization 
          correctness     | type checking 
*)

(******************************* Prop vs. Type ********************************)
    
(* In view of the Curry-Howard analogy, the reader could wonder if there is any 
actual difference between the two sorts Prop and Type in a system like the 
Calculus of Constructions, or if it just a matter of flavour. 

In fact there is a subtle difference concerning the type of product types over 
the given sorts. Consider for instance a higher order sentence of
the kind ∀P:Prop.P: this is just a sentence asserting that any proposition is 
true, and it looks natural to look at it as an object of sort Prop. However, if 
this is the case, when we are quantifying over ``all propositions' we are also 
implicitly quantifying over the proposition we are in the act of defining, that 
creates a strange and possibly dangerous circularity. 

In mathematics, definitions of this kind, where the definition (directly or 
indirectly) mentions or quantifies over the entity being defined are called 
"impredicative".

The opposite notion of impredicativity is "predicativity", which essentially 
entails building stratified (or ramified) theories where quantification over 
lower levels results in objects of some new type.

Impredicativity can be dangerous: a well known example is Russel's ``set of all 
sets'' resulting in famous logical paradox: does such a set contain itself as an 
element? If it does then by definition it should not, and if it does not then by 
definition it should.

A predicative approach would consist in distinguishing e.g. between ``small'' 
sets and ``large'' sets (collections), where the set of all small sets would 
result in a large set.

In fact, if we look at ∀P:Type[0].P$ as a dependent product, and we identify 
Type[0] as a universe of (small) ``sets'', it would seem strange to conclude 
that quantifying over all (small) sets we could obtain another (small) set. 

In Matita, ∀P:Type[0].P has in fact type Type[1] and not Type[0], where Type[1] 
is also the type of Type[0].

So, while Prop is impredicative, sorts of the kind Type[i] define a potentially 
infinite hierarchy of predicative sorts.

The difference between predicative and impredicative sorts is in the typing rule 
for the product ∏x:A.B: if the sort of B is Prop then ∏x:A.B has type Prop 
whatever the sort of A is; if A:Type[i] and B:Type[j], then ∏x:A.B:Type[k] where 
Type[k] is the smallest sort strictly larger than Type[i] and Type[j]:

   Γ ⊢ A : s    Γ,x:A ⊢ B:Prop         Γ ⊢ A : Type[i]    Γ,x:A ⊢ B:Type[j]
   ---------------------------         ------------------------------------
       Γ ⊢ ∏x:A.B : Prop                       Γ ⊢ ∏x:A.B : Type[k]

for k = max{i,j}+1.

It is worth to observe that in Matita, the index i is just a label: constraints 
among universes are declared by the user. The standard library (see 
"basics/pts.ma" declares a few of them, with the following relations:

     Type[0] < Type[1] < Type[2] < … 
     
The impredicativity of Prop is not a problem from the point of view of the 
logical consistency, but there is a price to be paid for this: we are not 
allowed to eliminate Prop vs. Type[i]. In concrete terms this means that while 
we are allowed to build terms, types or even propositions by structural 
induction on terms, the only think we can do by structural induction/case 
analysis on proofs is to build other proofs.

For instance, we know that a proof of p:A∨B is either a proof of A or a proof B, 
and one could be tempted to define a function that returns the boolean true in 
the first case and false otherwise, by performing a simple case analysis on p: 

definition discriminate_to_bool ≝ λA,B:Prop.λp:A∨B.
  match p with
  [ or_introl a ⇒ tt
  | or_intror b ⇒ ff
  ]. 

If you type the previous definition, Matita will complain with the following 
error message: ``TypeChecker failure: Sort elimination not allowed: Prop towards 
Type[0]''.
Even returning the two propositions True and False intead of two booleans would 
not work: 

definition discriminate_to_Prop ≝ λA,B:Prop.λp:A∨B.
 match p with
 [ or_introl a ⇒ True
 | or_intror b ⇒ False
 ].
 
The error message is the same as before: in both cases the sort of the branches 
is Type[0]. The only thing we can do is to return other proofs, like in the 
following example: *)

definition or_elim ≝ λA,B,C:Prop.λp:A∨B.λf:A→C.λg:B→C.
 match p with
 [ or_introl a ⇒ f a
 | or_intror b ⇒ g b
 ].

(* Exercise: repeat the previous examples in interactive mode, eliminating the
hypothesis p:A∨B. *)

(**************************** The axiom of choice *****************************)

(* The axiom of choice says that given a collection of non-empty sets S_i 
indexed over a base set I, it is possible to make a selection of exactly one
element x_i ∈ S_i. 
In type theory, this can be expressed in the following terms: *)

axiom choice_ax: ∀I:Type[0].∀S:I→Type[0].∀A:(∀i:I.S i → Type[0]).
  (∀i:I.(∑x:S i.A i x)) → ∑f:∀i:I.S i.∀i:I.A i (f i).

(* The axiom of choice is independent from the traditional basic axioms of set
theory, like Zermelo–Fraenkel set theory, hence, if required, must be explicitly
added to the theory. This extension of ZF, known as ZFC, provides the "standard" 
axiomatization of set theory. 

The controversial nature of the axiom of choice is related to the effectiveness
of performing the selection claimed by the axiom of choice; for this reasons the 
axiom of choice is usually rejected by constructive mathematicians. 

However, if the proof of the existence on an inhabitant x_i for each type S_i is
itself constructive, then this proof already provides a method that, when 
applied to an element i∈I returns the witness x_i. In other words, not only the
above axiom "choice" is perfectly acceptable, but it is actually provable! *)

theorem choice: ∀I:Type[0].∀S:I→Type[0].∀A.
  (∀i:I.∑x:S i.A i x) → ∑f:∀i:I.S i.∀i:I.A i (f i).
#I #S #A #H   
(* The goal is 
    ∑f:∀i:I.S i.(∀i:I.A i (f i))
We need to provide the function f:∀i:I.S i, and the proof that for any i:I, 
A i (f i). The hypothesis H tells us that for any i we can build an object 
(H i): ∑x:S i.A i x. The first projection of (H i) is an element of type (S i), 
and we may define f ≝ λi. DPair_fst … (H i).The second projection of (H i) is
a witness of A i (DPair_fst … (H i)), that is, according to our defintion 
of f, a witness of A i (f i). Hence, λi.DPair_snd ?? (H i): ∀i:I.A i (f i). *)
%{(λi.DPair_fst ?? (H i)) (λi.DPair_snd ?? (H i))}
qed.

(* It is worth to observe that if we try to repeat the same proof with either 
the existential of the sigma type it will not work. For instance, the 
following property is not provable: *)

axiom Pchoice: ∀I:Type[0].∀S:I→Type[0].∀A.
  (∀i:I.∃x:S i.A i x) → ∃f:∀i:I.S i.∀i:I.A i (f i).
  
(* The point is that the proof would require to extract from a non-informative
content, namely the fact that there exists an x such that (A i x), the actual 
witness x, that is an informative notion, and we know that this is forbidden for 
consistency reasons. *)





