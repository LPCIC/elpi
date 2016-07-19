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

include "basics/pts.ma".

inductive nat : Type[0] ≝ O: nat | S: nat → nat.

axiom test1: Type[1].

axiom test2: Type[1] → Type[1].

axiom test3: Prop → Type[1] → CProp[1] → Type[1] → Type[2].

axiom test4: ∀A:Type[1]. A → ∀B:Type[1]. B → ∀C:Prop. C → Type[1].

axiom test4': ∀C:Prop. C → C.

axiom test4'': ∀C:Prop. C → nat.

axiom test4''': ∀C:Type[1]. C.

axiom test4_5: (∀A:Type[0].A) → nat.

axiom test5: (Type[1] → Type[1]) → Type[1].

(* no content *)
axiom test6: Type[1] → Prop.

definition dtest1: Type[1] ≝ nat → nat.

definition dtest2: Type[2] ≝ ∀A:Type[1]. A → A.

definition dtest3: Type[1] → Type[1] ≝ λA:Type[1]. A → A.

definition dtest4: Type[1] → Type[1] ≝ λA:Type[1].dtest3 A.

definition dtest5: Type[1] → Type[1] ≝ dtest3.

definition dtest6: Type[1] ≝ dtest3 nat.

inductive True : Prop ≝ I: True.

(* no content *)
definition dtest7: Prop ≝ True → True.

(* no content *)
definition dtest8: Type[1] ≝ dtest3 True.

(* no content *)
definition dtest9: Type[1] ≝ dtest3 Prop.

definition dtest10: Type[1] → Type[1] → Type[1] ≝ λX,Y.X.

definition dtest11: Type[1] → nat → Type[1] → Type[1] ≝ λ_:Type[1].λ_:nat.λX:Type[1]. X → nat → test1.


definition dtest12 ≝ λ_:Type[1].λ_:nat.λX:Type[1]. X → nat → test1.

definition dtest13 ≝ dtest3 nat → dtest3 True → dtest3 Prop → nat.

definition dtest14 ≝ λX:Type[2]. X → X.

definition dtest15 ≝ ∀T:Type[1] → Type[1]. T nat → T nat.

definition dtest16 ≝ ∀T:Type[1]. T → nat.

definition dtest17 ≝ ∀T:dtest14 Type[1]. T nat → dtest14 nat → dtest14 nat.

definition dtest18 ≝ λA,B:Type[0].λn:nat.λC:Type[0].A.

definition dtest19 ≝ dtest18 nat True O nat → dtest18 nat nat O nat.

definition dtest20 ≝ test5 test2.

(*BUG: lambda-lift the inner declaration;
  to be traced, raises NotInFOmega; why?
definition dtest21 ≝ test5 (λX:Type[1].X).*)

definition ttest1 ≝ λx:nat.x.

(*BUG: clash of name due to capitalisation*)
(*definition Ttest1 ≝ λx:nat.x.*)

(*FEATURE: print binders in the l.h.s. without using lambda abstraction*)
definition ttest2 ≝ λT:Type[1].λx:T.x.

definition ttest3 ≝ λT:Type[1].λx:T.let y ≝ x in y.

definition ttest4 ≝ λT:Type[1].let y ≝ T in λx:y.x.

(*BUG IN HASKELL PRETTY PRINTING: all lets are let rec*)
(*definition ttest5 ≝ λT:Type[1].λy:T.let y ≝ y in y.*)

definition ttest6 ≝ ttest4 nat.

definition ttest7 ≝ λf:∀X:Type[1].X. f (nat → nat) O.

definition ttest8 ≝ λf:∀X:Type[1].X. f (True → True) I.

definition ttest9 ≝ λf:∀X:Type[1].X. f (True → nat) I.

definition ttest10 ≝ λf:∀X:Type[1].X. f (True → nat → nat) I O.

definition ttest11_aux ≝ λS:Type[1]. S → nat.

definition ttest11 ≝ λf:ttest11_aux True. f I.

definition ttest12 ≝ λf:True → nat. f I.

(*BUG: assertion failure here! difficult case for head application
axiom ttest13_a: ∀T:Type[1]. T → nat.
definition ttest13_b ≝ ttest13_a nat O.
definition ttest13_c ≝ ttest13_a Prop True.*)

(*GENERAL BUG: name clashes when binders shadow each other in CIC*)

(*BUG: for OCaml: cofixpoint not distinguished from fixpoints*)

let rec rtest1 (n:nat) : nat ≝
 match n with
 [ O ⇒ O
 | S m ⇒ rtest1 m ].

let rec f (n:nat) : nat ≝
 match n with
 [ O ⇒ O
 | S m ⇒ g m ]
and g (n:nat) : nat ≝
 match n with
 [ O ⇒ O
 | S m ⇒ f m ].

(*BUG: pattern matching patterns when arguments have been deleted from
  the constructor are wrong *)

coinductive stream: Type[0] ≝ scons : nat → stream → stream.

let corec div (n:nat) : stream ≝ scons n (div (S n)).

axiom plus: nat → nat → nat.

definition rtest2 : nat → stream → nat ≝
 λm,s. match s with [ scons n l ⇒ plus m n ].

(*
let rec mkterm (n:nat) : nat ≝
 match n with
 [ O ⇒ O
 | S m ⇒ mkterm m ]
and mktyp (n:nat) : Type[0] ≝
 match n with
 [ O ⇒ nat
 | S m ⇒ mktyp m ].*)

inductive meee: Type[0] → Type[0] ≝ .

inductive T1 : (Type[0] → Type[0]) → ∀B:Type[0]. nat → Type[0] → Type[0] ≝ .

inductive T2 : (Type[0] → Type[0]) → ∀B:Type[0]. B → Type[0] → Type[0] ≝ .

(* no content *)
inductive T3 : (Type[0] → Type[0]) → CProp[2] ≝ .

definition erase ≝ λX:Type[0].Type[0].

axiom lt: nat → nat → Prop.

inductive myvect (A: Type[0]) (b:nat) : nat → Type[0] ≝
   myemptyv : myvect A b O
 | mycons: ∀n. lt n b → A → myvect A b n → myvect A b (S n).
 
inductive False: Prop ≝ .

inductive Empty: Type[0] ≝ .

inductive bool: Type[0] ≝ true: bool | false:bool.

inductive eq (A:Type[1]) (a:A) : A → Prop ≝ refl: eq A a a.

(* requires coercion *)
definition cast_bug1 ≝
 λH:eq Type[0] bool nat. S (match H return λA:Type[0].λ_.A with [ refl ⇒ true ]).

(*
(*BUG: Here we use eq_rect_Type0 in its poly-kinded form, but we only extracted
   the one-kinded form. Require coercions *)
definition cast_bug1' ≝
 λH:eq Type[0] bool nat. S (eq_rect_Type0 Type[0] bool (λA:Type[0].λ_.A) true nat H).
*)

(* requires coercion in all branches *)
definition cast_bug2 ≝
  match true return λb.match b with [ true ⇒ nat → nat | false ⇒ bool ] with
   [ true ⇒ S | false ⇒ false ]
  O.
  
(*BUG: try singleton elimination with constructor arguments to show bug in
 DeBrujin indexes *)