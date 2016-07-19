(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "pts_dummy/reduction.ma".
(*
(*
inductive T : Type[0] ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
  | D: T →T
.
*)

inductive conv1 : T →T → Prop ≝
  | cbeta: ∀P,M,N. conv1 (App (Lambda P M) N) (M[0 ≝ N])
  | cappl: ∀M,M1,N. conv1 M M1 → conv1 (App M N) (App M1 N)
  | cappr: ∀M,N,N1. conv1 N N1 → conv1 (App M N) (App M N1)
  | claml: ∀M,M1,N. conv1 M M1 → conv1 (Lambda M N) (Lambda M1 N)
  | clamr: ∀M,N,N1. conv1 N N1 → conv1 (Lambda M N) (Lambda M N1)
  | cprodl: ∀M,M1,N. conv1 M M1 → conv1 (Prod M N) (Prod M1 N)
  | cprodr: ∀M,N,N1. conv1 N N1 → conv1 (Prod M N) (Prod M N1)
  | cd: ∀M,M1. conv1 (D M) (D M1). 

definition conv ≝ star … conv1.

lemma red_to_conv1: ∀M,N. red M N → conv1 M N.
#M #N #redMN (elim redMN) /2/
qed.

inductive d_eq : T →T → Prop ≝
  | same: ∀M. d_eq M M
  | ed: ∀M,M1. d_eq (D M) (D M1)
  | eapp: ∀M1,M2,N1,N2. d_eq M1 M2 → d_eq N1 N2 → 
      d_eq (App M1 N1) (App M2 N2)
  | elam: ∀M1,M2,N1,N2. d_eq M1 M2 → d_eq N1 N2 → 
      d_eq (Lambda M1 N1) (Lambda M2 N2)
  | eprod: ∀M1,M2,N1,N2. d_eq M1 M2 → d_eq N1 N2 → 
      d_eq (Prod M1 N1) (Prod M2 N2).
      
lemma conv1_to_deq: ∀M,N. conv1 M N → red M N ∨ d_eq M N.
#M #N #coMN (elim coMN)
  [#P #B #C %1 //
  |#P #M1 #N1 #coPM1 * [#redP %1 /2/ | #eqPM1 %2 /3/]
  |#P #M1 #N1 #coPM1 * [#redP %1 /2/ | #eqPM1 %2 /3/]
  |#P #M1 #N1 #coPM1 * [#redP %1 /2/ | #eqPM1 %2 /3/]
  |#P #M1 #N1 #coPM1 * [#redP %1 /2/ | #eqPM1 %2 /3/]
  |#P #M1 #N1 #coPM1 * [#redP %1 /2/ | #eqPM1 %2 /3/]
  |#P #M1 #N1 #coPM1 * [#redP %1 /2/ | #eqPM1 %2 /3/]
  |#P #M1 %2 //
  ]
qed.

(* FG: THIS IS NOT COMPLETE
theorem main1: ∀M,N. conv M N → 
  ∃P,Q. star … red M P ∧ star … red N Q ∧ d_eq P Q.
#M #N #coMN (elim coMN)
  [#B #C #rMB #convBC * #P1 * #Q1 * * #redMP1 #redBQ1 
   #deqP1Q1 (cases (conv_to_deq … convBC))
    [
  |@(ex_intro … M) @(ex_intro … M) % // % //
  ]
*)
*)
