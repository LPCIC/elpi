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

include "pts_dummy_new/subterms.ma".

(*
inductive T : Type[0] ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
  | D: T →T →T
. *)

(*
let rec is_dummy M ≝ 
match M with 
  [D P ⇒ true
  |_ ⇒ false
  ]. *)
  
let rec is_lambda M ≝ 
match M with 
  [Lambda P Q ⇒ true
  |_ ⇒ false
  ]. 

(* 
theorem is_dummy_to_exists: ∀M. is_dummy M = true → 
∃N. M = D N.
#M (cases M) normalize 
  [1,2: #n #H destruct|3,4,5: #P #Q #H destruct
  |#N #_ @(ex_intro … N) //
  ]
qed.*)

theorem is_lambda_to_exists: ∀M. is_lambda M = true → 
∃P,N. M = Lambda P N.
#M (cases M) normalize 
  [1,2: #n #H destruct|3,5,6: #P #Q #H destruct
  |#P #N #_ @(ex_intro … P) @(ex_intro … N) //
  ]
qed. 

inductive pr : T →T → Prop ≝
  | beta: ∀P,M,N,M1,N1. pr M M1 → pr N N1 →
      pr (App (Lambda P M) N) (M1[0 ≝ N1])
  | none: ∀M. pr M M
  | appl: ∀M,M1,N,N1. pr M M1 → pr N N1 → pr (App M N) (App M1 N1)
  | lam: ∀P,P1,M,M1. pr P P1 → pr M M1 → 
      pr (Lambda P M) (Lambda P1 M1)
  | prod: ∀P,P1,M,M1. pr P P1 → pr M M1 → 
      pr (Prod P M) (Prod P1 M1)
  | d: ∀M,M1,N,N1. pr M M1 → pr N N1 → pr (D M N) (D M1 N1).

lemma prSort: ∀M,n. pr (Sort n) M → M = Sort n.
#M #n #prH (inversion prH)
  [#P #M #N #M1 #N1 #_ #_ #_ #_ #H destruct
  |//
  |3,4,5,6: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  ]
qed.

lemma prRel: ∀M,n. pr (Rel n) M → M = Rel n.
#M #n #prH (inversion prH)
  [#P #M #N #M1 #N1 #_ #_ #_ #_ #H destruct
  |//
  |3,4,5,6: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  ]
qed.

lemma prD: ∀M,N,P. pr (D M N) P → 
  ∃M1,N1.P = D M1 N1 ∧ pr M M1 ∧ pr N N1.
#M #N #P #prH (inversion prH)  
  [#P #M #N #M1 #N1 #_ #_ #_ #_ #H destruct
  |#Q #eqQ #_ @(ex_intro … M) @(ex_intro … N) /3/ 
  |3,4,5: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  |#M1 #M2 #N1 #N2 #pr1 #pr2 #_ #_ #H destruct #eqP 
   @(ex_intro … M2) @(ex_intro … N2) /3/
  ]
qed.
(* BEGIN HERE
lemma prApp_not_lambda: 
∀M,N,P. pr (App M N) P → is_lambda M = false →
  ∃M1,N1. (P = App M1 N1 ∧ pr M M1 ∧ pr N N1).
#M #N #P #prH (inversion prH)
  [#P #M #N #M1 #N1 #_ #_ #_ #_ #H destruct #_ #H1 destruct
  |#M1 #eqM1 #_ #_ @(ex_intro … M) @(ex_intro … N) /3/ 
  |#M1 #N1 #M2 #N2 #pr1 #pr2 #_ #_ #H #H1 #_ destruct 
   @(ex_intro … N1) @(ex_intro … N2) /3/ 
  |4,5,6: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  ]
qed. 

lemma prApp_lambda: 
∀Q,M,N,P. pr (App (Lambda Q M) N) P → 
  ∃M1,N1. (P = M1[0:=N1] ∧ pr M M1 ∧ pr N N1) ∨
   (P = (App M1 N1) ∧ pr (Lambda Q M) M1 ∧ pr N N1).
#Q #M #N #P #prH (inversion prH)
  [#R #M #N #M1 #N1 #pr1 #pr2 #_ #_ #H destruct #_ 
   @(ex_intro … M1) @(ex_intro … N1) /4/ 
  |#M1 #eqM1 #_ @(ex_intro … (Lambda Q M)) @(ex_intro … N) /4/ 
  |#M1 #N1 #M2 #N2 #pr1 #pr2 #_ #_ #H destruct #_
   @(ex_intro … N1) @(ex_intro … N2) /4/ 
  |4,5,6: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  ]
qed. 

lemma prLambda: ∀M,N,P. pr (Lambda M N) P →
  ∃M1,N1. (P = Lambda M1 N1 ∧ pr M M1 ∧ pr N N1).
#M #N #P #prH (inversion prH)
  [#P #M #N #M1 #N1 #_ #_ #_ #_ #H destruct 
  |#Q #eqQ #_ @(ex_intro … M) @(ex_intro … N) /3/
  |3,5,6: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  |#Q #Q1 #S #S1 #pr1 #pr2 #_ #_ #H #H1 destruct 
   @(ex_intro … Q1) @(ex_intro … S1) /3/
  ]
qed. 

lemma prProd: ∀M,N,P. pr (Prod M N) P → 
  ∃M1,N1. P = Prod M1 N1 ∧ pr M M1 ∧ pr N N1.
#M #N #P #prH (inversion prH)
  [#P #M #N #M1 #N1 #_ #_ #_ #_ #H destruct 
  |#Q #eqQ #_ @(ex_intro … M) @(ex_intro … N) /3/
  |3,4,6: #M #M1 #N #N1 #_ #_ #_ #_ #H destruct
  |#Q #Q1 #S #S1 #pr1 #pr2 #_ #_ #H #H1 destruct
   @(ex_intro … Q1) @(ex_intro … S1) /3/
  ]
qed.
 
let rec full M ≝
  match M with
  [ Sort n ⇒ Sort n
  | Rel n ⇒ Rel n
  | App P Q ⇒ full_app P (full Q)
  | Lambda P Q ⇒ Lambda (full P) (full Q)
  | Prod P Q ⇒ Prod (full P) (full Q)
  | D P Q ⇒ D (full P) (full Q)
  ]
and full_app M N ≝
  match M with 
  [ Sort n ⇒ App (Sort n) N
  | Rel n ⇒ App (Rel n) N
  | App P Q ⇒ App (full_app P (full Q)) N
  | Lambda P Q ⇒ (full Q) [0 ≝ N] 
  | Prod P Q ⇒ App (Prod (full P) (full Q)) N
  | D P Q ⇒ App (D (full P) (full Q)) N
  ]
. 

lemma pr_lift: ∀N,N1,n. pr N N1 → 
  ∀k. pr (lift N k n) (lift N1 k n).
#N #N1 #n #pr1 (elim pr1)
  [#P #M1 #N1 #M2 #N2 #pr2 #pr3 #Hind1 #Hind2 #k
   normalize >lift_subst_up @beta; // 
  |// 
  |#M1 #N1 #M2 #N2 #pr2 #pr3 #Hind1 #Hind2 #k
   normalize @appl; [@Hind1 |@Hind2]
  |#M1 #N1 #M2 #N2 #pr2 #pr3 #Hind1 #Hind2 #k
   normalize @lam; [@Hind1 |@Hind2]
  |#M1 #N1 #M2 #N2 #pr2 #pr3 #Hind1 #Hind2 #k
   normalize @prod; [@Hind1 |@Hind2]
  |#M1 #N1 #M2 #N2 #pr2 #pr3 #Hind1 #Hind2 #k
   normalize @d; [@Hind1 |@Hind2]
  ]
qed.

theorem pr_subst: ∀M,M1,N,N1,n. pr M M1 → pr N N1 → 
  pr M[n≝N] M1[n≝N1].
@Telim_size #P (cases P) 
  [#i #Hind #N #M1 #N1 #n #pr1 #pr2 >(prSort … pr1) //
  |#i #Hind #N #M1 #N1 #n #pr1 #pr2 >(prRel … pr1)
    (cases (true_or_false (leb i n)))
    [#lein (cases (le_to_or_lt_eq i n (leb_true_to_le … lein)))
      [#ltin >(subst_rel1 … ltin) >(subst_rel1 … ltin) //
      |#eqin >eqin >subst_rel2 >subst_rel2 /2/ 
      ]
    |#lefalse (cut (n < i)) [@not_le_to_lt /2/] #ltni
     >(subst_rel3 … ltni) >(subst_rel3 … ltni) //
    ]
  |#Q #M #Hind #M1 #N #N1 #n #pr1 #pr2
   (cases (true_or_false (is_lambda Q)))
    [#islambda (cases (is_lambda_to_exists … islambda))
     #M2 * #N2 #eqQ >eqQ in pr1 #pr3 (cases (prApp_lambda … pr3))
     #M3 * #N3 * 
      [* * #eqM1 #pr4 #pr5 >eqM1 
       >(plus_n_O n) in ⊢ (??%) >subst_lemma @beta;
        [<plus_n_O @Hind // >eqQ 
         @(transitive_lt ? (size (Lambda M2 N2))) normalize //
        |@Hind // normalize // 
        ]
      |* * #eqM1 #pr4 #pr5 >eqM1 @appl;  
        [@Hind // <eqQ normalize // 
        |@Hind // normalize // 
        ]
      ]
    |#notlambda (cases (prApp_not_lambda … pr1 ?)) //
     #M2 * #N2 * * #eqM1 #pr3 #pr4 >eqM1 @appl;
      [@Hind // normalize // |@Hind // normalize // ]
    ]
  |#Q #M #Hind #M1 #N #N1 #n #pr1 #pr2
   (cases (prLambda … pr1))
   #N2 * #Q1 * * #eqM1 #pr3 #pr4 >eqM1 @lam;
    [@Hind // normalize // | @Hind // normalize // ]
  |#Q #M #Hind #M1 #N #N1 #n #pr1 #pr2
   (cases (prProd … pr1)) #M2 * #N2 * * #eqM1 #pr3 #pr4 >eqM1
   @prod; [@Hind // normalize // | @Hind // normalize // ]
  |#Q #M #Hind #M1 #N #N1 #n #pr1 #pr2 
   (cases (prD … pr1)) #M2 * #N2 * * #eqM1 #pr3 #pr4 >eqM1 
   @d; [@Hind // normalize // | @Hind // normalize // ] 
  ]
qed.
 
lemma pr_full_app: ∀M,N,N1. pr N N1 → 
  (∀S.subterm S M → pr S (full S)) →
  pr (App M N) (full_app M N1).
#M (elim M) normalize /2/
  [#P #Q #Hind1 #Hind2 #N1 #N2 #prN #H @appl // @Hind1 /3/
  |#P #Q #Hind1 #Hind2 #N1 #N2 #prN #H @beta /2/
  |#P #Q #Hind1 #Hind2 #N1 #N2 #prN #H @appl // @prod /2/
  |#P #Q #Hind1 #Hind2 #N1 #N2 #prN #H @appl // @d /2/
  ]
qed.

theorem pr_full: ∀M. pr M (full M).
@Telim #M (cases M) normalize
  [// 
  |//
  |#M1 #N1 #H @pr_full_app /3/
  |#M1 #N1 #H normalize /3/
  |#M1 #N1 #H @prod /2/
  |#M1 #N1 #H @d /2/ 
  ]
qed. 

lemma complete_app: ∀M,N,P.
  (∀S,P.subterm S (App M N) → pr S P → pr P (full S)) →
  pr (App M N) P → pr P (full_app M (full N)).
#M (elim M) normalize
  [#n #P #Q #subH #pr1 cases (prApp_not_lambda … pr1 ?) // 
   #M1 * #N1 * * #eqQ #pr1 #pr2 >eqQ @appl; 
    [@(subH (Sort n)) // |@subH //]
  |#n #P #Q #subH #pr1 cases (prApp_not_lambda … pr1 ?) // 
   #M1 * #N1 * * #eqQ #pr1 #pr2 >eqQ @appl; 
    [@(subH (Rel n)) // |@subH //]
  |#P #Q #Hind1 #Hind2 #N1 #N2 #subH #prH
   cases (prApp_not_lambda … prH ?) // 
   #M2 * #N2 * * #eqQ #pr1 #pr2 >eqQ @appl; 
    [@Hind1 /3/ |@subH //]
  |#P #Q #Hind1 #Hind2 #N1 #P2 #subH #prH
   cases (prApp_lambda … prH) #M2 * #N2 *
    [* * #eqP2 #pr1 #pr2 >eqP2 @pr_subst /3/
    |* * #eqP2 #pr1 #pr2 >eqP2 (cases (prLambda … pr1))
     #M3 * #M4 * * #eqM2 #pr3 #pr4 >eqM2 @beta @subH /2/
    ]
  |#P #Q #Hind1 #Hind2 #N1 #N2 #subH #prH
   cases (prApp_not_lambda … prH ?) // 
   #M2 * #N2 * * #eqQ #pr1 #pr2 >eqQ @appl; 
    [@(subH (Prod P Q)) // |@subH //]
  |#P #Q #Hind1 #Hind2 #N1 #N2 #subH #pr1
   cases (prApp_not_lambda … pr1 ?) // 
   #M1 * #N1 * * #eqQ #pr2 #pr3 >eqQ @appl; 
    [@(subH (D P Q) M1) // |@subH //]    
  ]
qed.

theorem complete: ∀M,N. pr M N → pr N (full M).
@Telim #M (cases M) 
  [#n #Hind #N #prH normalize >(prSort … prH) //
  |#n #Hind #N #prH normalize >(prRel … prH) //
  |#M #N #Hind #Q @complete_app 
   #S #P #subS @Hind //
  |#P #P1 #Hind #N #Hpr 
   (cases (prLambda …Hpr)) #M1 * #N1 * * #eqN >eqN normalize /3/
  |#P #P1 #Hind #N #Hpr 
   (cases (prProd …Hpr)) #M1 * #N1 * * #eqN >eqN normalize /3/
  |#P #P1 #Hind #N #Hpr
   (cases (prD …Hpr)) #M1 * #N1 * * #eqN >eqN normalize /3/
  ]
qed.

theorem diamond: ∀P,Q,R. pr P Q → pr P R → ∃S.
pr Q S ∧ pr P S.
#P #Q #R #pr1 #pr2 @(ex_intro … (full P)) /3/
qed.
*)
