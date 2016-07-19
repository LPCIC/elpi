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

include "pts_dummy_new/par_reduction.ma".
include "basics/star.ma".

(*
inductive T : Type[0] ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
  | D: T →T
. *)

inductive red : T →T → Prop ≝
  | rbeta: ∀P,M,N. red (App (Lambda P M) N) (M[0 ≝ N])
  | rappl: ∀M,M1,N. red M M1 → red (App M N) (App M1 N)
  | rappr: ∀M,N,N1. red N N1 → red (App M N) (App M N1)
  | rlaml: ∀M,M1,N. red M M1 → red (Lambda M N) (Lambda M1 N)
  | rlamr: ∀M,N,N1. red N N1 → red(Lambda M N) (Lambda M N1)
  | rprodl: ∀M,M1,N. red M M1 → red (Prod M N) (Prod M1 N)
  | rprodr: ∀M,N,N1. red N N1 → red (Prod M N) (Prod M N1)
  | dl: ∀M,M1,N. red M M1 → red (D M N) (D M1 N)
  | dr: ∀M,N,N1. red N N1 → red (D M N) (D M N1).

lemma red_to_pr: ∀M,N. red M N → pr M N.
#M #N #redMN (elim redMN) /2/
qed.

lemma red_d : ∀M,N,P. red (D M N) P → 
  (∃M1. P = D M1 N ∧ red M M1) ∨
  (∃N1. P = D M N1 ∧ red N N1).
#M #N #P #redMP (inversion redMP)
  [#P1 #M1 #N1 #eqH destruct
  |2,3,4,5,6,7:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP 
   %1 @(ex_intro … M1) /2/
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP 
   %2 @(ex_intro … N1) /2/
  ]
qed.

lemma red_lambda : ∀M,N,P. red (Lambda M N) P →
 (∃M1. P = (Lambda M1 N) ∧ red M M1) ∨
 (∃N1. P = (Lambda M N1) ∧ red N N1).
#M #N #P #redMNP (inversion redMNP)
  [#P1 #M1 #N1 #eqH destruct
  |2,3,6,7,8,9:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %1 
   (@(ex_intro … M1)) % //
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %2
   (@(ex_intro … N1)) % //
  ]
qed.
  
lemma red_prod : ∀M,N,P. red (Prod M N) P →
 (∃M1. P = (Prod M1 N) ∧ red M M1) ∨
 (∃N1. P = (Prod M N1) ∧ red N N1).
#M #N #P #redMNP (inversion redMNP)
  [#P1 #M1 #N1 #eqH destruct
  |2,3,4,5,8,9:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %1
   (@(ex_intro … M1)) % //
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %2 
   (@(ex_intro … N1)) % //
  ]
qed.

lemma red_app : ∀M,N,P. red (App M N) P →
 (∃M1,N1. M =  (Lambda M1 N1) ∧ P = N1[0:=N]) ∨
 (∃M1. P = (App M1 N) ∧ red M M1) ∨
 (∃N1. P = (App M N1) ∧ red N N1).
#M #N #P #redMNP (inversion redMNP)
  [#P1 #M1 #N1 #eqH destruct #eqP %1 %1 
   @(ex_intro … P1) @(ex_intro … M1) % //
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %1 %2
   (@(ex_intro … M1)) % //
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %2 
   (@(ex_intro … N1)) % //
  |4,5,6,7,8,9:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  ]
qed.

definition reduct ≝ λn,m. red m n.

definition SN : T → Prop ≝ WF ? reduct.

definition NF : T → Prop ≝ λM. ∀N. ¬ (reduct N M).

theorem NF_to_SN: ∀M. NF M → SN M.
#M #nfM % #a #red @False_ind /2/
qed.

lemma NF_Sort: ∀i. NF (Sort i).
#i #N % #redN (inversion redN) 
  [1: #P #N #M #H destruct
  |2,3,4,5,6,7,8,9: #N #M #P #_ #_ #H destruct
  ]
qed.

lemma NF_Rel: ∀i. NF (Rel i).
#i #N % #redN (inversion redN) 
  [1: #P #N #M #H destruct
  |2,3,4,5,6,7,8,9: #N #M #P #_ #_ #H destruct
  ]
qed.

lemma red_subst : ∀N,M,M1,i. red M M1 → red M[i≝N] M1[i≝N].
#N @Telim_size #P (cases P) 
  [1,2:#j #Hind #M1 #i #r1 @False_ind /2/
  |#P #Q #Hind #M1 #i #r1 (cases (red_app … r1))
    [*
      [* #M2 * #N2 * #eqP #eqM1 >eqP normalize
       >eqM1 >(plus_n_O i) >(subst_lemma N2) <(plus_n_O i)
       (cut (i+1 =S i)) [//] #Hcut >Hcut @rbeta
      |* #M2 * #eqM1 #rP >eqM1 normalize @rappl @Hind /2/
      ]
    |* #N2 * #eqM1 #rQ >eqM1 normalize @rappr @Hind /2/
    ] 
  |#P #Q #Hind #M1 #i #r1 (cases (red_lambda …r1)) 
    [* #P1 * #eqM1 #redP >eqM1 normalize @rlaml @Hind /2/
    |* #Q1 * #eqM1 #redP >eqM1 normalize @rlamr @Hind /2/
    ]
  |#P #Q #Hind #M1 #i #r1 (cases (red_prod …r1))
    [* #P1 * #eqM1 #redP >eqM1 normalize @rprodl @Hind /2/
    |* #P1 * #eqM1 #redP >eqM1 normalize @rprodr @Hind /2/
    ]
  |#P #Q #Hind #M1 #i #r1 (cases (red_d …r1))
    [* #P1 * #eqM1 #redP >eqM1 normalize @dl @Hind /2/
    |* #P1 * #eqM1 #redP >eqM1 normalize @dr @Hind /2/
    ]
qed.

lemma red_lift: ∀N,N1,n. red N N1 → ∀k. red (lift N k n) (lift N1 k n).
#N #N1 #n #r1 (elim r1) normalize /2/
qed.

(* star red *)
lemma star_appl: ∀M,M1,N. star … red M M1 → 
  star … red (App M N) (App M1 N).
#M #M1 #N #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/ 
qed.
  
lemma star_appr: ∀M,N,N1. star … red N N1 →
  star … red (App M N) (App M N1).
#M #N #N1 #star1 (elim star1) // 
#B #C #starMB #redBC #H /3 width=3/
qed.
 
lemma star_app: ∀M,M1,N,N1. star … red M M1 → star … red N N1 → 
  star … red (App M N) (App M1 N1).
#M #M1 #N #N1 #redM #redN @(trans_star ??? (App M1 N)) /2/
qed.

lemma star_laml: ∀M,M1,N. star … red M M1 → 
  star … red (Lambda M N) (Lambda M1 N).
#M #M1 #N #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/ 
qed.
  
lemma star_lamr: ∀M,N,N1. star … red N N1 →
  star … red (Lambda M N) (Lambda M N1).
#M #N #N1 #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/
qed.
 
lemma star_lam: ∀M,M1,N,N1. star … red M M1 → star … red N N1 → 
  star … red (Lambda M N) (Lambda M1 N1).
#M #M1 #N #N1 #redM #redN @(trans_star ??? (Lambda M1 N)) /2/
qed.

lemma star_prodl: ∀M,M1,N. star … red M M1 → 
  star … red (Prod M N) (Prod M1 N).
#M #M1 #N #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/
qed.
  
lemma star_prodr: ∀M,N,N1. star … red N N1 →
  star … red (Prod M N) (Prod M N1).
#M #N #N1 #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/
qed.
 
lemma star_prod: ∀M,M1,N,N1. star … red M M1 → star … red N N1 → 
  star … red (Prod M N) (Prod M1 N1).
#M #M1 #N #N1 #redM #redN @(trans_star ??? (Prod M1 N)) /2/
qed.

lemma star_dl: ∀M,M1,N. star … red M M1 → 
  star … red (D M N) (D M1 N).
#M #M1 #N #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/
qed.
  
lemma star_dr: ∀M,N,N1. star … red N N1 →
  star … red (D M N) (D M N1).
#M #N #N1 #star1 (elim star1) //
#B #C #starMB #redBC #H /3 width=3/
qed.

lemma star_d: ∀M,M1,N,N1. star … red M M1 → star … red N N1 → 
  star … red (D M N) (D M1 N1).
#M #M1 #N #N1 #redM #redN @(trans_star ??? (D M1 N)) /2/
qed.

lemma red_subst1 : ∀M,N,N1,i. red N N1 → 
 (star … red) M[i≝N] M[i≝N1].
#M (elim M)
  [// 
  |#i #P #Q #n #r1 (cases (true_or_false (leb i n)))
    [#lein (cases (le_to_or_lt_eq i n (leb_true_to_le … lein)))
      [#ltin >(subst_rel1 … ltin) >(subst_rel1 … ltin) //
      |#eqin >eqin >subst_rel2 >subst_rel2 @R_to_star /2/
      ]
    |#lefalse (cut (n < i)) [@not_le_to_lt /2/] #ltni
     >(subst_rel3 … ltni) >(subst_rel3 … ltni) //
    ]
  |#P #Q #Hind1 #Hind2 #M1 #N1 #i #r1 normalize @star_app /2/ 
  |#P #Q #Hind1 #Hind2 #M1 #N1 #i #r1 normalize @star_lam /2/
  |#P #Q #Hind1 #Hind2 #M1 #N1 #i #r1 normalize @star_prod /2/
  |#P #Q #Hind1 #Hind2 #M1 #N1 #i #r1 normalize @star_d /2/
  ]
qed. 

lemma SN_d : ∀M. SN M → ∀N. SN N → SN (D M N). 
#M #snM (elim snM) #b #H #Hind 
#N #snN (elim snN) #c #H1 #Hind1 % #a #redd 
(cases (red_d … redd))
  [* #Q * #eqa #redbQ >eqa @Hind // % /2/
  |* #Q * #eqa #redbQ >eqa @Hind1 //
  ]
qed. 

lemma SN_step: ∀N. SN N → ∀M. reduct M N → SN M.
#N * #b #H #M #red @H //.
qed. 

lemma SN_star: ∀M,N. (star … red) N M → SN N → SN M.
#M #N #rstar (elim rstar) //
#Q #P #HbQ  #redQP #snNQ #snN @(SN_step …redQP) /2/
qed. 

lemma sub_red: ∀M,N.subterm N M → ∀N1.red N N1 → 
∃M1.subterm N1 M1 ∧ red M M1.
#M #N #subN (elim subN) /4/
(* trsansitive case *)
#P #Q #S #subPQ #subQS #H1 #H2 #A #redP (cases (H1 ? redP))
#B * #subA #redQ (cases (H2 ? redQ)) #C * #subBC #redSC
@(ex_intro … C) /3/
qed.

axiom sub_star_red: ∀M,N.(star … subterm) N M → ∀N1.red N N1 → 
∃M1.subterm N1 M1 ∧ red M M1.
  
lemma SN_subterm: ∀M. SN M → ∀N.subterm N M → SN N.
#M #snM (elim snM) #M #snM #HindM #N #subNM % #N1 #redN 
(cases (sub_red … subNM ? redN)) #M1 *
#subN1M1 #redMM1 @(HindM … redMM1) //
qed.

lemma SN_subterm_star: ∀M. SN M → ∀N.(star … subterm N M) → SN N.
#M #snM #N #Hstar (cases (star_inv T subterm M N)) #_ #H
lapply (H Hstar) #Hstari (elim Hstari) //
#M #N #_ #subNM #snM @(SN_subterm …subNM) //
qed.

definition shrink ≝ λN,M. reduct N M ∨ (TC … subterm) N M.

definition SH ≝ WF ? shrink.

lemma SH_subterm: ∀M. SH M → ∀N.(star … subterm) N M → SH N.
#M #snM (elim snM) #M 
#snM #HindM #N #subNM (cases (star_case ???? subNM))
  [#eqNM >eqNM % /2/
  |#subsNM % #N1 *
    [#redN (cases (sub_star_red … subNM ? redN)) #M1 *
     #subN1M1 #redMM1 @(HindM M1) /2/
    |#subN1 @(HindM N) /2/ 
    ]
  ]
qed.

theorem SN_to_SH: ∀N. SN N → SH N.
#N #snN (elim snN) (@Telim_size) 
#b #Hsize #snb #Hind % #a * /2/ #subab @Hsize; 
  [(elim subab) 
    [#c #subac @size_subterm // 
    |#b #c #subab #subbc #sab @(transitive_lt … sab) @size_subterm //
    ]    
  |@SN_step @(SN_subterm_star b); 
    [% /2/ |@TC_to_star @subab] % @snb
  |#a1 #reda1 cases(sub_star_red b a ?? reda1);
    [#a2 * #suba1 #redba2 @(SH_subterm a2) /2/ |/2/ ]  
  ]
qed.

lemma SH_to_SN: ∀N. SH N → SN N.
@WF_antimonotonic /2/ qed.

lemma SN_Lambda: ∀N.SN N → ∀M.SN M → SN (Lambda N M).
#N #snN (elim snN) #P #shP #HindP #M #snM 
(* for M we proceed by induction on SH *)
(lapply (SN_to_SH ? snM)) #shM (elim shM)
#Q #shQ #HindQ % #a #redH (cases (red_lambda … redH))
  [* #S * #eqa #redPS >eqa @(HindP S ? Q ?) // 
   @SH_to_SN % /2/ 
  |* #S * #eqa #redQS >eqa @(HindQ S) /2/
  ]
qed. 
 
lemma SN_Prod: ∀N.SN N → ∀M.SN M → SN (Prod N M).
#N #snN (elim snN) #P #shP #HindP #M #snM (elim snM)
#Q #snQ #HindQ % #a #redH (cases (red_prod … redH))
  [* #S * #eqa #redPS >eqa @(HindP S ? Q ?) // 
   % /2/ 
  |* #S * #eqa #redQS >eqa @(HindQ S) /2/
  ]
qed.

lemma SN_subst: ∀i,N,M.SN M[i ≝ N] → SN M.
#i #N (cut (∀P.SN P → ∀M.P=M[i ≝ N] → SN M)); 
  [#P #H (elim H) #Q #snQ #Hind #M #eqM % #M1 #redM 
   @(Hind M1[i:=N]) // >eqM /2/
  |#Hcut #M #snM @(Hcut … snM) //
qed.

(*
lemma SN_DAPP: ∀N,M. SN (App M N) → SN (App (D M) N).
cut (∀P. SN P → ∀M,N. P = App M N → SN (App (D M) N)); [|/2/]
#P #snP (elim snP) #Q #snQ #Hind
#M #N #eqQ % #A #rA (cases (red_app … rA))
  [* 
    [*
      [* #M1 * #N1 * #eqH destruct
      |* #M1 * #eqH destruct #eqA >eqA @SN_d % @snQ
      ]
    |* #M1 * #eqA #red1 (cases (red_d …red1))
     #M2 * #eqM1 #r2 >eqA >eqM1 @(Hind (App M2 N)) /2/
    ]
  |* #M2 * #eqA >eqA #r2 @(Hind (App M M2)) /2/
  ]
qed. *)

lemma  SN_APP: ∀P.SN P → ∀N. SN N → ∀M.
  SN M[0:=N] → SN (App (Lambda P M) N).
#P #snP (elim snP) #A #snA #HindA
#N #snN (elim snN) #B #snB #HindB
#M #snM1 (cut (SH M)) [@SN_to_SH @(SN_subst … snM1)] #shM 
generalize in match snM1; elim shM
#C #shC #HindC #snC1 % #Q #redQ cases (red_app … redQ);
  [*
    [* #M2 * #N2 * #eqlam destruct #eqQ //
    |* #M2 * #eqQ #redlam >eqQ (cases (red_lambda …redlam))
      [* #M3 * #eqM2 #r2 >eqM2 @HindA // % /2/
      |* #M3 * #eqM2 #r2 >eqM2 @HindC; 
        [%1 // |@(SN_step … snC1) /2/]
      ]
    ]
  |* #M2 * #eqQ #r2 >eqQ @HindB // @(SN_star … snC1) 
   @red_subst1 //
  ]
qed.




