(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "turing/basic_machines.ma".
include "turing/if_machine.ma".

(* while {
     if current != null 
        then move_r
        else nop
     }
 *)

definition mte_step ≝ λalpha,D.
ifTM ? (test_null alpha) (single_finalTM ? (move alpha D)) (nop ?) tc_true.
 
definition R_mte_step_true ≝ λalpha,D,t1,t2.
  ∃ls,c,rs.
    t1 = midtape alpha ls c rs ∧ t2 = tape_move ? t1 D.

definition R_mte_step_false ≝ λalpha.λt1,t2:tape alpha.
  current ? t1 = None ? ∧ t1 = t2.

definition mte_acc : ∀alpha,D.states ? (mte_step alpha D) ≝ 
λalpha,D.(inr … (inl … (inr … start_nop))).
  
lemma sem_mte_step :
  ∀alpha,D.mte_step alpha D ⊨ 
   [ mte_acc … : R_mte_step_true alpha D, R_mte_step_false alpha ] .
#alpha #D #ta
@(acc_sem_if_app ??????????? (sem_test_null …) 
  (sem_move_single …) (sem_nop alpha) ??)
[ #tb #tc #td * #Hcurtb
  lapply (refl ? (current ? tb)) cases (current ? tb) in ⊢ (???%→?);
  [ #H @False_ind >H in Hcurtb; * /2/ ]
  -Hcurtb #c #Hcurtb #Htb whd in ⊢ (%→?); #Htc whd
  cases (current_to_midtape … Hcurtb) #ls * #rs #Hmidtb 
  %{ls} %{c} %{rs} % //
| #tb #tc #td * #Hcurtb #Htb whd in ⊢ (%→?); #Htc whd % // ]
qed.

definition move_to_end ≝ λsig,D.whileTM sig (mte_step sig D) (mte_acc …).

definition R_move_to_end_r ≝ 
  λsig,int,outt.
  (current ? int = None ? → outt = int) ∧
  ∀ls,c,rs.int = midtape sig ls c rs → outt = mk_tape ? (reverse ? rs@c::ls) (None ?) [ ].
  
lemma wsem_move_to_end_r : ∀sig. move_to_end sig R ⊫ R_move_to_end_r sig.
#sig #ta #k #outc #Hloop
lapply (sem_while … (sem_mte_step sig R) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ * #Hcurtb #Houtc % /2/ #ls #c #rs #Htb >Htb in Hcurtb; normalize in ⊢ (%→?); #H destruct (H)
| #tc #td * #ls * #c * #rs * #Htc >Htc cases rs
  [ normalize in ⊢ (%→?); #Htd >Htd #Hstar #IH whd in ⊢ (%→?); #Hfalse
    lapply (IH Hfalse) -IH * #Htd1 #_ %
    [ normalize in ⊢ (%→?); #H destruct (H)
    | #ls0 #c0 #rs0 #H destruct (H) >Htd1 // ]
  | #r0 #rs0 whd in ⊢ (???%→?); #Htd >Htd #Hstar #IH whd in ⊢ (%→?); #Hfalse
    lapply (IH Hfalse) -IH * #_ #IH %
    [ normalize in ⊢ (%→?); #H destruct (H)
    | #ls1 #c1 #rs1 #H destruct (H) >reverse_cons >associative_append @IH % ] ] ]
qed.

lemma terminate_move_to_end_r :  ∀sig,t.move_to_end sig R ↓ t.
#sig #t @(terminate_while … (sem_mte_step sig R …)) //
cases t
[ % #t1 * #ls * #c * #rs * #H destruct
|2,3: #a0 #al0 % #t1 * #ls * #c * #rs * #H destruct
| #ls #c #rs lapply c -c lapply ls -ls elim rs
  [ #ls #c % #t1 * #ls0 * #c0 * #rs0 * #Hmid #Ht1 destruct %
    #t2 * #ls1 * #c1 * #rs1 * normalize in ⊢ (%→?); #H destruct
  | #r0 #rs0 #IH #ls #c % #t1 * #ls1 * #c1 * #rs1 * #Hmid #Ht1 destruct @IH
  ]
]
qed.

lemma sem_move_to_end_r : ∀sig. move_to_end sig R ⊨ R_move_to_end_r sig.
#sig @WRealize_to_Realize //
qed.

definition R_move_to_end_l ≝ 
  λsig,int,outt.
  (current ? int = None ? → outt = int) ∧
  ∀ls,c,rs.int = midtape sig ls c rs → outt = mk_tape ? [ ] (None ?) (reverse ? ls@c::rs).
  
lemma wsem_move_to_end_l : ∀sig. move_to_end sig L ⊫ R_move_to_end_l sig.
#sig #ta #k #outc #Hloop
lapply (sem_while … (sem_mte_step sig L) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ * #Hcurtb #Houtc % /2/ #ls #c #rs #Htb >Htb in Hcurtb; normalize in ⊢ (%→?); #H destruct (H)
| #tc #td * #ls * #c * #rs * #Htc >Htc cases ls
  [ normalize in ⊢ (%→?); #Htd >Htd #Hstar #IH whd in ⊢ (%→?); #Hfalse
    lapply (IH Hfalse) -IH * #Htd1 #_ %
    [ normalize in ⊢ (%→?); #H destruct (H)
    | #ls0 #c0 #rs0 #H destruct (H) >Htd1 // ]
  | #l0 #ls0 whd in ⊢ (???%→?); #Htd >Htd #Hstar #IH whd in ⊢ (%→?); #Hfalse
    lapply (IH Hfalse) -IH * #_ #IH %
    [ normalize in ⊢ (%→?); #H destruct (H)
    | #ls1 #c1 #rs1 #H destruct (H) >reverse_cons >associative_append @IH % ] ] ]
qed.

lemma terminate_move_to_end_l :  ∀sig,t.move_to_end sig L ↓ t.
#sig #t @(terminate_while … (sem_mte_step sig L …)) //
cases t
[ % #t1 * #ls * #c * #rs * #H destruct
|2,3: #a0 #al0 % #t1 * #ls * #c * #rs * #H destruct
| #ls elim ls
  [ #c #rs % #t1 * #ls0 * #c0 * #rs0 * #Hmid #Ht1 destruct %
    #t2 * #ls1 * #c1 * #rs1 * normalize in ⊢ (%→?); #H destruct
  | #l0 #ls0 #IH #c #rs % #t1 * #ls1 * #c1 * #rs1 * #Hmid #Ht1 destruct @IH
  ]
]
qed.

lemma sem_move_to_end_l : ∀sig. move_to_end sig L ⊨ R_move_to_end_l sig.
#sig @WRealize_to_Realize //
qed.

