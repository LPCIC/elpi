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

inductive False: CProp[0] ≝.

inductive Or (A,B:CProp[0]) : CProp[0] ≝
 | Left : A → Or A B
 | Right : B → Or A B.

interpretation "constructive or" 'or x y = (Or x y).

inductive Or3 (A,B,C:CProp[0]) : CProp[0] ≝
 | Left3 : A → Or3 A B C
 | Middle3 : B → Or3 A B C
 | Right3 : C → Or3 A B C.

interpretation "constructive ternary or" 'or3 x y z= (Or3 x y z).

notation < "hvbox(a break ∨ b break ∨ c)" with precedence 35 for @{'or3 $a $b $c}.

inductive Or4 (A,B,C,D:CProp[0]) : CProp[0] ≝
 | Left3 : A → Or4 A B C D
 | Middle3 : B → Or4 A B C D
 | Right3 : C → Or4 A B C D
 | Extra3: D → Or4 A B C D.

interpretation "constructive ternary or" 'or4 x y z t = (Or4 x y z t).

notation < "hvbox(a break ∨ b break ∨ c break ∨ d)" with precedence 35 for @{'or4 $a $b $c $d}.

inductive And (A,B:CProp[0]) : CProp[0] ≝
 | Conj : A → B → And A B.
 
interpretation "constructive and" 'and x y = (And x y).

inductive And3 (A,B,C:CProp[0]) : CProp[0] ≝
 | Conj3 : A → B → C → And3 A B C.

notation < "hvbox(a break ∧ b break ∧ c)" with precedence 35 for @{'and3 $a $b $c}.
 
interpretation "constructive ternary and" 'and3 x y z = (And3 x y z).

inductive And42 (A,B,C,D:CProp[2]) : CProp[2] ≝
 | Conj42 : A → B → C → D → And42 A B C D.

notation < "hvbox(a break ∧ b break ∧ c break ∧ d)" with precedence 35 for @{'and4 $a $b $c $d}.
 
interpretation "constructive quaternary and2" 'and4 x y z t = (And42 x y z t).

record Iff (A,B:CProp[0]) : CProp[0] ≝
 { if: A → B;
   fi: B → A
 }.
 
record Iff1 (A,B:CProp[1]) : CProp[1] ≝
 { if1: A → B;
   fi1: B → A
 }.
 
notation "hvbox(a break ⇔ b)" right associative with precedence 25 for @{'iff1 $a $b}.
interpretation "logical iff" 'iff x y = (Iff x y).
interpretation "logical iff type1" 'iff1 x y = (Iff1 x y).

inductive exT22 (A:Type[2]) (P:A→CProp[2]) : CProp[2] ≝
  ex_introT22: ∀w:A. P w → exT22 A P.
  
interpretation "CProp[2] exists" 'exists \eta.x = (exT22 ? x).
(*
definition pi1exT22 ≝ λA,P.λx:exT22 A P.match x with [ex_introT22 x _ ⇒ x].
definition pi2exT22 ≝ 
  λA,P.λx:exT22 A P.match x return λx.P (pi1exT22 ?? x) with [ex_introT22 _ p ⇒ p].
  
interpretation "exT22 \fst" 'pi1 = (pi1exT22 ? ?).
interpretation "exT22 \snd" 'pi2 = (pi2exT22 ? ?).
interpretation "exT22 \fst a" 'pi1a x = (pi1exT22 ? ? x).
interpretation "exT22 \snd a" 'pi2a x = (pi2exT22 ? ? x).
interpretation "exT22 \fst b" 'pi1b x y = (pi1exT22 ? ? x y).
interpretation "exT22 \snd b" 'pi2b x y = (pi2exT22 ? ? x y).
*)
inductive exT (A:Type[0]) (P:A→CProp[0]) : CProp[0] ≝
  ex_introT: ∀w:A. P w → exT A P.

interpretation "CProp exists" 'exists \eta.x = (exT ? x).

notation "\ll term 19 a, break term 19 b \gg" 
with precedence 90 for @{'dependent_pair $a $b}.
interpretation "dependent pair" 'dependent_pair a b = 
  (ex_introT ? ? a b).

(*
definition pi1exT ≝ λA,P.λx:exT A P.match x with [ex_introT x _ ⇒ x].
definition pi2exT ≝ 
  λA,P.λx:exT A P.match x return λx.P (pi1exT ?? x) with [ex_introT _ p ⇒ p].

interpretation "exT \fst" 'pi1 = (pi1exT ? ?).
interpretation "exT \fst a" 'pi1a x = (pi1exT ? ? x).
interpretation "exT \fst b" 'pi1b x y = (pi1exT ? ? x y).
interpretation "exT \snd" 'pi2 = (pi2exT ? ?).
interpretation "exT \snd a" 'pi2a x = (pi2exT ? ? x).
interpretation "exT \snd b" 'pi2b x y = (pi2exT ? ? x y).
*)
inductive exT23 (A:Type[0]) (P:A→CProp[0]) (Q:A→CProp[0]) (R:A→A→CProp[0]) : CProp[0] ≝
  ex_introT23: ∀w,p:A. P w → Q p → R w p → exT23 A P Q R.
(*
definition pi1exT23 ≝
  λA,P,Q,R.λx:exT23 A P Q R.match x with [ex_introT23 x _ _ _ _ ⇒ x].
definition pi2exT23 ≝
  λA,P,Q,R.λx:exT23 A P Q R.match x with [ex_introT23 _ x _ _ _ ⇒ x].

interpretation "exT2 \fst" 'pi1 = (pi1exT23 ? ? ? ?).
interpretation "exT2 \snd" 'pi2 = (pi2exT23 ? ? ? ?).   
interpretation "exT2 \fst a" 'pi1a x = (pi1exT23 ? ? ? ? x).
interpretation "exT2 \snd a" 'pi2a x = (pi2exT23 ? ? ? ? x).
interpretation "exT2 \fst b" 'pi1b x y = (pi1exT23 ? ? ? ? x y).
interpretation "exT2 \snd b" 'pi2b x y = (pi2exT23 ? ? ? ? x y).
*)
inductive exT2 (A:Type[0]) (P,Q:A→CProp[0]) : CProp[0] ≝
  ex_introT2: ∀w:A. P w → Q w → exT2 A P Q.


definition Not : CProp[0] → CProp[0] ≝ λx:CProp[0].x → False.

interpretation "constructive not" 'not x = (Not x).
  
definition cotransitive: ∀C:Type[0]. ∀lt:C→C→CProp[0].CProp[0] ≝
 λC:Type[0].λlt:C→C→CProp[0].∀x,y,z:C. lt x y → lt x z ∨ lt z y. 

definition coreflexive: ∀C:Type[0]. ∀lt:C→C→CProp[0].CProp[0] ≝
 λC:Type[0].λlt:C→C→CProp[0]. ∀x:C. ¬ (lt x x).

definition symmetric: ∀C:Type[0]. ∀lt:C→C→CProp[0].CProp[0] ≝
 λC:Type[0].λlt:C→C→CProp[0]. ∀x,y:C.lt x y → lt y x.

definition antisymmetric: ∀A:Type[0]. ∀R:A→A→CProp[0]. ∀eq:A→A→Prop.CProp[0] ≝
 λA:Type[0].λR:A→A→CProp[0].λeq:A→A→Prop.∀x:A.∀y:A.R x y→R y x→eq x y.

definition reflexive: ∀C:Type[0]. ∀lt:C→C→CProp[0].CProp[0] ≝ λA:Type[0].λR:A→A→CProp[0].∀x:A.R x x.

definition transitive: ∀C:Type[0]. ∀lt:C→C→CProp[0].CProp[0] ≝ λA:Type[0].λR:A→A→CProp[0].∀x,y,z:A.R x y → R y z → R x z.

definition reflexive1: ∀A:Type[1].∀R:A→A→CProp[1].CProp[1] ≝ λA:Type[1].λR:A→A→CProp[1].∀x:A.R x x.
definition symmetric1: ∀A:Type[1].∀R:A→A→CProp[1].CProp[1] ≝ λC:Type[1].λlt:C→C→CProp[1]. ∀x,y:C.lt x y → lt y x.
definition transitive1: ∀A:Type[1].∀R:A→A→CProp[1].CProp[1] ≝ λA:Type[1].λR:A→A→CProp[1].∀x,y,z:A.R x y → R y z → R x z.

definition reflexive2: ∀A:Type[2].∀R:A→A→CProp[2].CProp[2] ≝ λA:Type[2].λR:A→A→CProp[2].∀x:A.R x x.
definition symmetric2: ∀A:Type[2].∀R:A→A→CProp[2].CProp[2] ≝ λC:Type[2].λlt:C→C→CProp[2]. ∀x,y:C.lt x y → lt y x.
definition transitive2: ∀A:Type[2].∀R:A→A→CProp[2].CProp[2] ≝ λA:Type[2].λR:A→A→CProp[2].∀x,y,z:A.R x y → R y z → R x z.

definition reflexive3: ∀A:Type[3].∀R:A→A→CProp[3].CProp[3] ≝ λA:Type[3].λR:A→A→CProp[3].∀x:A.R x x.
definition symmetric3: ∀A:Type[3].∀R:A→A→CProp[3].CProp[3] ≝ λC:Type[3].λlt:C→C→CProp[3]. ∀x,y:C.lt x y → lt y x.
definition transitive3: ∀A:Type[3].∀R:A→A→CProp[3].CProp[3] ≝ λA:Type[3].λR:A→A→CProp[3].∀x,y,z:A.R x y → R y z → R x z.
