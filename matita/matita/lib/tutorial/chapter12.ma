(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/relations.ma".
include "basics/types.ma".
include "arithmetics/nat.ma".
include "hints_declaration.ma".

(******************* Quotienting in type theory **********************)

(* One fundamental operation in set theory is quotienting: given a set S
 and an equivalence relation R over S, quotienting creates a new set S/R
 whose elements are equivalence classes of elements of S. The idea behind
 quotienting is to replace the structural equality over S with R, therefore
 identifying elements up to R. The use of equivalence classes is just a
 technicality.
 
 The type theory of Matita does not have quotient types. In the litterature
 there are alternative proposals to introduce quotient types, but no consensus
 have been reached yet. Nevertheless, quotient types can be dispensed and
 replaced by setoids. A setoid is defined as a type S coupled with an
 equivalence relation R, used to compare elements of S. In place of working
 with equivalence classes of S up to R, one keeps working with elements of S,
 but compares them using R in place of =. Setoids over types (elements of
 Type[0]) can be declared in Matita as follows. *)

record equivalence_relation (A: Type[0]) : Type[0] ≝ {
    eqrel:> relation A
  ; equiv_refl: reflexive … eqrel
  ; equiv_sym: symmetric … eqrel
  ; equiv_trans: transitive … eqrel
}.

record setoid : Type[1] ≝ {
    carrier:> Type[0]
  ; eq_setoid: equivalence_relation carrier
}.

(* Note that carrier has been defined as a coercion so that when S is a setoid
 we can write x:S in place of x: carrier S. *)

(* We use the notation ≃ for the equality on setoid elements. *)
notation "hvbox(n break ≃ m)"
  non associative with precedence 45
for @{ 'congruent $n $m }.

interpretation "eq_setoid" 'congruent n m = (eqrel ? (eq_setoid ?) n m).

(* Example: integers as pairs of naturals (n,m) quotiented by
   (n1,m1) ≝ (n2,m2) iff n1 + m2 = m1 + n2. The integer +n is represented
   by any pair (k,n+k), while the integer -n by any pair (n+k,n).
   The three proof obligations are to prove reflexivity, symmetry and
   transitivity. Only the latter is not closed by automation. *)
definition Z: setoid ≝
 mk_setoid (ℕ × ℕ)
  (mk_equivalence_relation …
   (λc1,c2. \fst c1 + \snd c2 = \fst c2 + \snd c1) …).
 whd // * #x1 #x2 * #y1 #y2 * #z1 #z3 #H1 #H2
 cut (x1 + y2 + y1 + z3 = y1 + x2 + z1 + y2) // #H3
 cut ((y2 + y1) + (x1 + z3) = (y2 + y1) + (z1 + x2)) // #H4
 @(injective_plus_r … H4)
qed.

(* The two integers (0,1) and (1,2) are equal up to ≃, written
   〈0,1〉 ≃ 〈1,2〉. Unfolding the notation, that corresponds to
   eqrel ? (eq_setoid ?) 〈0,1〉 〈1,2〉 which means that the two
   pairs are to be compare according to the equivalence relation
   of an unknown setoid ? whose carrier is ℕ × ℕ. An hint can be
   used to always pick Z as the setoid for ℕ × ℕ. *)

unification hint 0 ≔ ;
    X ≟ Z
(* ---------------------------------------- *) ⊢
    ℕ × ℕ ≡ carrier X.

(* Thanks to the hint, Matita now accepts the statement. *)
example ex1: 〈0,1〉 ≃ 〈1,2〉.
 //
qed.

(* Every type is a setoid when elements are compared up to Leibniz equality. *)
definition LEIBNIZ: Type[0] → setoid ≝
 λA.
  mk_setoid A
   (mk_equivalence_relation … (eq …) …).
 //
qed.

(* Note that we declare the hint with a lower precedence level (10 vs 0,
 precedence levels are in decreasing order). In this way an ad-hoc setoid
 hint will be always preferred to the Leibniz one. for example,
 〈0,1〉 ≃ 〈1,2〉 is still interpreted in Z, while 1 ≃ 2 is interpreted as 1=2. *)
unification hint 10 ≔ A: Type[0];
    X ≟ LEIBNIZ A
(* ---------------------------------------- *) ⊢
    A ≡ carrier X.

(* Propositions up to coimplication form a setoid. *)
definition PROP: setoid ≝
 mk_setoid Prop
  (mk_equivalence_relation … (λx,y. x ↔ y) …).
 whd [ @iff_trans | @iff_sym | /2/ ]
qed.

unification hint 0 ≔ ;
    X ≟ PROP
(* ---------------------------------------- *) ⊢
    Prop ≡ carrier X.

(* In set theory functions and relations over a quotient S/R can be defined
  by lifting a function/relation over S that respects R. Respecting R means that
  the relations holds for an element x of S iff it holds for every y of S such
  that x R y. Similarly, a function f respects R iff f x = f y for every x,y
  such that x R y. In type theory propositions are just special cases of
  functions whose codomain is Prop. 
  
  Note that in the definition of respect for functions in set theory f x and
  f y are compared using =. When working with setoids in type theory we need
  to systematically abandon = in favour of ≃, unless we know in advance that
  a certain type taken in input is never going to be quotiented. We say that
  a function between two setoids is proper when it respects their equalities. *)

definition proper: ∀I,O:setoid. (I → O) → Prop ≝
 λI,O,f. ∀x,y:I. x ≃ y → f x ≃ f y.
 
(* A proper function is called a morphism. *)
record morphism (I,O: setoid) : Type[0] ≝ {
   mor_carr:1> I → O
 ; mor_proper: proper … mor_carr
 }.

(* We introduce a notation for morphism using the symbols of an arrow followed by a dot. *)
notation "hvbox(I break ⤞ O)"
  right associative with precedence 20
for @{ 'morphism $I $O }.

interpretation "morphism" 'morphism I O = (morphism I O).

(* By declaring mor_carr as a coercion it is possible to write f x for
   mor_carr f x in order to apply a morphism f to an argument. *)

(* Example: opposite of an integer number. We first implement the function
  over Z and then lift it to a morphism. The proof obligation is to prove
  properness. *)
definition opp: Z → Z ≝ λc.〈\snd c,\fst c〉.

definition OPP: Z ⤞ Z ≝ mk_morphism … opp ….
 normalize //
qed.

(* When writing expressions over Z we will always use the function opp, that
 does not carry additional information. The following hints will be automatically
 used by the system to retrieve the morphism associated to opp when needed, i.e.
 to retrieve the proof of properness of opp. This is a use of unification hints
 to implement automatic proof search. The first hint is used when the function
 is partially applied, the second one when it is applied to an argument. *)

unification hint 0 ≔ ;
    X ≟ OPP
(* ---------------------------------------- *) ⊢
    opp ≡ mor_carr … X.

unification hint 0 ≔ x:Z ;
    X ≟ OPP
(* ---------------------------------------- *) ⊢
    opp x ≡ mor_carr … X x.

(* Example: we state that opp is proper and we will prove it without using
 automation and without referring to OPP. When we apply the universal mor_proper
 property of morphisms, Matita looks for the morphism associate to opp x and
 finds it thanks to the second unification hint above, completing the proof. *)
example ex2: ∀x,y. x ≃ y → opp x ≃ opp y.
 #x #y #EQ @mor_proper @EQ
qed.

(* The previous definition of proper only deals with unary functions. In type
 theory n-ary functions are better handled in Curryfied form as unary functions
 whose output is a function space type. When we restrict to morphisms, we do not
 need a notion of properness for n-ary functions because the function space can
 also be seen as a setoid quotienting functions using functional extensionality:
 two morphisms are equal when they map equal elements to equal elements. *)
definition function_space: setoid → setoid → setoid ≝
 λI,O.
  mk_setoid (I ⤞ O)
   (mk_equivalence_relation … (λf,g. ∀x,y:I. x ≃ y → f x ≃ g y) …).
 whd
 [ #f1 #f2 #f3 #f1_f2 #f2_f3 #x #y #EQ @(equiv_trans … (f2 x)) /2/
 | #f1 #f2 #f1_f2 #x #y #EQ @(equiv_sym … (f1_f2 …)) @equiv_sym //
 | #f #x #y #EQ @mor_proper // ]
qed.

unification hint 0 ≔ I,O: setoid;
    X ≟ function_space I O
(* ---------------------------------------- *) ⊢
    I ⤞ O ≡ carrier X.

(* We overload the notation so that I ⤞ O can mean both the type of morphisms
 from I to O or the function space from I to O. *)
interpretation "function_space" 'morphism I O = (function_space I O).

(* A binary morphism is just obtained by Currification. In the following
 we will use I1 ⤞ I2 ⤞ O directly in place of bin_morphism. *)
definition bin_morphism: setoid → setoid → setoid → Type[0] ≝
 λI1,I2,O. I1 ⤞ I2 ⤞ O.

(* Directly inhabiting a binary morphism is annoying because one needs to
 write a function that returns a morphism in place of a binary function.
 Moreover, there are two proof obligations to prove. We can simplify the work
 by introducing a new constructor for binary morphisms that takes in input a
 binary function and opens a single proof obligation, called proper2. *)
definition proper2: ∀I1,I2,O: setoid. (I1 → I2 → O) → Prop ≝
 λI1,I2,O,f.
  ∀x1,x2,y1,y2. x1 ≃ x2 → y1 ≃ y2 → f x1 y1 ≃ f x2 y2.
  
definition mk_bin_morphism:
 ∀I1,I2,O: setoid. ∀f: I1 → I2 → O. proper2 … f → I1 ⤞ I2 ⤞ O ≝
λI1,I2,O,f,proper.
  mk_morphism … (λx. mk_morphism … (λy. f x y) …) ….
 normalize /2/
qed.

(* We can also coerce a binary morphism to a binary function and prove that
 proper2 holds for every binary morphism. *)
definition binary_function_of_binary_morphism:
 ∀I1,I2,O: setoid. (I1 ⤞ I2 ⤞ O) → (I1 → I2 → O) ≝
λI1,I2,O,f,x,y. f x y.

coercion binary_function_of_binary_morphism:
 ∀I1,I2,O: setoid. ∀f:I1 ⤞ I2 ⤞ O. (I1 → I2 → O) ≝
 binary_function_of_binary_morphism
 on _f: ? ⤞ ? ⤞ ? to ? → ? → ?.

theorem mor_proper2: ∀I1,I2,O: setoid. ∀f: I1 ⤞ I2 ⤞ O. proper2 … f.
 #I2 #I2 #O #f #x1 #x2 #y1 #y2 #EQx #EQy @(mor_proper … f … EQx … EQy)
qed. 

(* Example: addition of integer numbers. We define addition as a function
 before lifting it to a morphism and declaring the hints to automatically
 prove it proper when needed. *)
definition Zplus: Z → Z → Z ≝ λx,y. 〈\fst x + \fst y,\snd x + \snd y〉.

(* We overload + over integers. *)
interpretation "Zplus" 'plus x y = (Zplus x y).

definition ZPLUS: Z ⤞ Z ⤞ Z ≝ mk_bin_morphism … Zplus ….
 normalize * #x1a #x1b * //
qed.

unification hint 0 ≔ x,y:Z ;
    X ≟ ZPLUS
(* ---------------------------------------- *) ⊢
    x + y ≡ mor_carr … X x y.

(* The identity function is a morphism and composition of morphisms is also
 a morphism. This means that the identity function is always proper and
 a compound context is proper if every constituent is. *)
definition id_morphism: ∀S: setoid. S ⤞ S ≝
 λS. mk_morphism … (λx.x) ….
 //
qed.

definition comp_morphism: ∀S1,S2,S3. (S2 ⤞ S3) → (S1 ⤞ S2) → (S1 ⤞ S3) ≝
 λS1,S2,S3,f1,f2. mk_morphism … (λx. f1 (f2 x)) ….
 normalize #x1 #x2 #EQ @mor_proper @mor_proper //
qed.

(*
(* The following hint is an example of proof automation rule. It says that
 f1 (f2 x) can be seen to be the application of the morphism
 comp_morphism F1 F2 to x as long as two morphisms F1 and F2 can be
 associated to f1 and f2. *)
unification hint 0 ≔
 S1,S2,S3: setoid, f1: S2 → S3, f2: S1 → S2, x:S1, F1: S2 ⤞ S3, F2: S1 ⤞ S2;
    f1 ≟ mor_carr … F1,
    f2 ≟ mor_carr … F2,
    X ≟ comp_morphism … F1 F2
(* ---------------------------------------- *) ⊢
    f1 (f2 x) ≡ mor_carr … X x. *)

(* By iterating applications of mor_proper, we can consume the context bit by
 bit in order to perform a rewriting. Like in ex2, the script works on any
 setoid because it does not reference OPP anywhere. The above theorem on
 composition of morphisms justify the correctness of the scripts. *)
example ex3: ∀x,y. x ≃ y → opp (opp (opp x)) ≃ opp (opp (opp y)).
 #x #y #EQ @mor_proper @mor_proper @mor_proper @EQ
qed.

(* We can improve the readability of the previous script by assigning
 a notation to mor_proper and by packing together the various applications
 of mor_proper and EQ. We pick the prefix symbol †. *)
notation "† c" with precedence 90 for @{'proper $c }.

interpretation "mor_proper" 'proper c  = (mor_proper ????? c).

example ex3': ∀x,y. x ≃ y → opp (opp (opp x)) ≃ opp (opp (opp y)).
 #x #y #EQ @(†(†(†EQ)))
qed.

(* While the term (†(†(†EQ))) can seem puzzling at first, note that it
 closely matches the term (opp (opp (opp x))). Each occurrence of the
 unary morphism opp is replaced by † and the occurrence x to be rewritten to y
 is replaced by EQ: x ≃ y. Therefore the term (†(†(†EQ))) is a compact
 notation to express at once where the rewriting should be performed and
 what hypothesis should be used for the rewriting. We will explain now
 the problem of rewriting setoid equalities in full generality, and a lightweight
 solution to it. *)

(****** Rewriting setoid equalities *********)

(* In set theory, once a quotient S/R has been defined, its elements are
 compared using the standard equality = whose main property is that of replacing
 equals to equals in every context. If E1=E2 then f E1 can be replaced with f E2
 for every context f. Note that f is applied to equivalence classes of elements
 of S. Therefore every function and property in f must have been lifted to work
 on equivalence classes, and this was possible only if f respected R.
 
 When using setoids we keep working with elements of S instead of forming a new
 type. Therefore, we must deal with contexts f that are not proper. When f is
 not proper, f E1 cannot be replaced with f E2 even if E1 ≃ E2. For example,
 〈0,1〉 ≃ 〈1,2〉 but \fst 〈0,1〉 ≠ \fst 〈1,2〉. Therefore every time we want to
 rewrite E1 with E2 under the assumption that E1 ≃ E2 we need to prove the
 context to be proper. Most of the time the context is just a composition of
 morphisms and, like in ex3', the only information that the user needs to
 give to the system is the position of the occurrences of E1 to be replaced
 and the equations to be used for the rewriting. As for ex3', we can provide
 a simple syntax to describe contexts and equations at the same time. The
 syntax is just given by a few notations to hide applications of mor_proper,
 reflexivity, symmetry and transitivity.

 Here is a synopsis of the syntax:
 -  †_   to rewrite in the argument of a unary morphism
 - _‡_   to rewrite in both arguments of a binary morphism
 -  #    to avoid rewriting in this position
 -  t    to rewrite from left to right in this position using the proof t.
         Usually t is the name of an hypothesis in the context of type E1 ≃ E2
 - t^-1  to rewrite from right to left in this position using the proof t.
         Concretely, it applies symmetry to t, proving E2 ≃ E1 from E1 ≃ E2.
 - ._    to start rewriting when the goal is not an equation ≃.
         Concretely, it applies the proof of P E2 → P E1 obtained by splitting
         the double implication P E2 ↔ P E1, which is equivalent to P E2 ≃ P E1
         where ≃ is the equality of the PROP setoid. Thus the argument should
         be a proof of P E2 ≃ P E1, obtained using the previous symbols according
         to the shape of P.
 - .=_   to prove an equation G1 ≃ G2 by first rewriting into E1 leaving a new
         goal G1' ≃ G2. Concretely, it applies transitivity of ≃.
*)

notation "l ‡ r" with precedence 90 for @{'proper2 $l $r }.

interpretation "mor_proper2" 'proper2 x y = (mor_proper ? (function_space ? ?) ?? ? x ?? y).

notation "#" with precedence 90 for @{'reflex}.

interpretation "reflexivity" 'reflex = (equiv_refl ???).

interpretation "symmetry" 'invert r = (equiv_sym ???? r).

notation ".= r" with precedence 55 for @{'trans $r}.

interpretation "transitivity" 'trans r = (equiv_trans ????? r ?).

notation ". r" with precedence 55 for @{'fi $r}.

definition fi: ∀A,B:Prop. A ≃ B → (B → A) ≝ λA,B,r. proj2 ?? r.

interpretation "fi" 'fi r = (fi ?? r).

(* The following example shows several of the features at once:
   1. the first occurrence of x2 is turned into x1 by rewriting the hypothesis
      from right to left.
   2. the first occurrence of x1 is turned into x2 by rewriting the hypothesis
      from left to right.
   3. the two rewritings are performed at once.
   4. the subterm z+y does not need to be rewritten. Therefore a single # is
      used in place of #‡#, which is also correct but produces a larger proof.
   5. we can directly start with an application of ‡ because the goal is a
      setoid equality *)
example ex4: ∀x1,x2,y,z:Z. x1 ≃ x2 →
 (y + x2) + (x1 + (z + y)) ≃ (y + x1) + (x2 + (z + y)).
 #x1 #x2 #y #z #EQ @((#‡EQ^-1)‡(EQ‡#))
qed.

(* The following example is just to illustrate the use of .=. We prove the
 same statement of ex4, but this time we perform one rewriting at a time.
 Note that in an intermediate goal Matita replaces occurrences of Zplus with
 occurrences of (the carrier of) ZPLUS. To recover the notation + it is
 sufficient to expand the declaration of ZPLUS. *)
example ex5: ∀x1,x2,y,z:Z. x1 ≃ x2 →
 (y + x2) + (x1 + (z + y)) ≃ (y + x1) + (x2 + (z + y)).
 #x1 #x2 #y #z #EQ @(.=(#‡EQ^-1)‡#) whd in match ZPLUS; @(#‡(EQ‡#))
qed.

(* Our last example involves rewriting under a predicate different from ≃.
 We first introduce such a predicate over integers. *)
definition is_zero: Z → Prop ≝ λc. \fst c = \snd c.

definition IS_ZERO: Z ⤞ PROP ≝ mk_morphism … is_zero ….
 normalize /3 by conj,injective_plus_r/
qed.

unification hint 0 ≔ x:Z ;
    X ≟ IS_ZERO
(* ---------------------------------------- *) ⊢
    is_zero x ≡ mor_carr … X x.

(* We can rewrite under any predicate starting with . *)
example ex6: ∀x,y:Z. x ≃ y → is_zero (x + y) → is_zero (x + x).
 #x #y #EQ #H @(.†(#‡EQ)) @H
qed.

(****** Dependent setoids ********)

(* A setoid is essentially a type equipped with its own notion of equality.
 In a dependent type theory, one expects to be able to both build types (and
 setoids) dependent on other types (and setoids). Working with families of
 setoids that depend over a plain type --- i.e. not another setoid --- pauses
 no additional problem. For example, we can build a setoid out of vectors of
 length n assigning to it the type ℕ → setoid. All the machinery for setoids
 just introduced keeps working. On the other hand, types that depend over a
 setoid require a much more complex machinery and, in practice, it is not
 advised to try to work with them in an intentional type theory like the one
 of Matita.
 
 To understand the issue, imagine that we have defined a family of
 types I dependent over integers: I: Z → Type. Because 〈0,1〉 and 〈1,2〉 both
 represent the same integer +1, the two types I 〈0,1〉 and of I 〈1,2〉 should have
 exactly the same inhabitants. However, being different types, their inhabitants
 are disjoint. The solution is to equip the type I with a transport function
 t: ∀n,m:Z. n ≃ m → I n → I m  that maps an element of I n to the corresponding
 element of I m. Starting from this idea, the picture quickly becomes complex
 when one start considering all the additional equations that the transport
 functions should satisfy. For example, if p: n ≃ m, then t … p (t … p^-1 x) = x,
 i.e. the element in I n corresponding to the element in I m that corresponds to
 x in I n should be exactly x. Moreover, for any function f: ∀n. I n → T n for
 some other type T dependent over n the following equation should hold:
 f … (t … p x) = t … p (f … x) (i.e. transporting and applying f should commute
 because f should be insensitive too up to ≃ to the actual representation of the
 integral indexes).

 Luckily enough, in practice types dependent overs setoids occur very rarely.
 Most examples of dependent types are indexed over discrete objects, like
 natural, integers and rationals, that admit an unique representation.
 For continuity reasons, types dependent over real numbers can also be
 represented as types dependent over a dense subset of the reals, like the
 rational numbers. *)

(****** Avoiding setoids *******)

(* Quotients are used pervasively in mathematics. In many practical situations,
 for example when dealing with finite objects like pairs of naturals, an unique
 representation can be imposed, for example by introducing a normalization
 procedure to be called after every operation. For example, integer numbers can
 be normalized to either 〈0,n〉 or 〈n,0〉. Or they can be represented as either 0
 or a non zero number, with the latter being encoded by a boolean (the sign) and
 a natural (the predecessor of the absolute value). For example, -3 would be
 represented by NonZero 〈false,2〉, +3 by NonZero 〈true,2〉 and 0 by Zero.
 Rational numbers n/m can be put in normal form by dividing both n and m by their
 greatest common divisor, or by picking n=0, m=1 when n is 0. These normal form
 is an unique representation.
 
 Imposing an unique representation is not always possible. For example, picking
 a canonical representative for a Cauchy sequence is not a computable operation.
 Nevertheless, when possible, avoiding setoids is preferrable:
 1) when the Leibniz equality is used, replacing n with m knowing n=m does not
    require any proof of properness
 2) at the moment automation in Matita is only available for Leibniz equalities.
    By switching to setoids less proofs are automatically found
 3) types dependent over plain types do not need ad-hoc transport functions
    because the rewriting principle for Leibniz equality plays that role and
    already satisfies for free all required equations
 4) normal forms are usually smaller than other forms. By sticking to normal
    forms both the memory consumption and the computational cost of operations
    may be reduced. *)
