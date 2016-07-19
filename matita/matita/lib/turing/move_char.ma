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


(* MOVE_CHAR RIGHT MACHINE

Sposta il carattere binario su cui si trova la testina appena prima del primo # alla sua destra.

Input:
(ls,cs,rs can be empty; # is a parameter)

  ls x cs # rs
       ^
Output:
  ls cs x # rs
        ^
Initial state = 〈0,#〉
Final state = 〈4,#〉

*)

include "turing/basic_machines.ma".
include "turing/if_machine.ma".

definition mcr_step ≝ λalpha:FinSet.λsep:alpha.
  ifTM alpha (test_char ? (λc.¬c==sep))
     (single_finalTM … (swap_l alpha sep · move_r ?)) (nop ?) tc_true.

definition Rmcr_step_true ≝ 
  λalpha,sep,t1,t2. 
   ∃b. b ≠ sep ∧
    ((∃a,ls,rs.
       t1 = midtape alpha (a::ls) b rs ∧
       t2 = mk_tape alpha (a::b::ls) (option_hd ? rs) (tail ? rs)) ∨
     (∃rs.
       t1 = midtape alpha [ ] b rs ∧
       t2 = leftof alpha b rs)).

definition Rmcr_step_false ≝ 
  λalpha,sep,t1,t2.
    left ? t1 ≠ [] →  current alpha t1 ≠ None alpha → 
      current alpha t1 = Some alpha sep ∧ t2 = t1.
      
lemma sem_mcr_step :
  ∀alpha,sep.
  mcr_step alpha sep ⊨ 
    [inr … (inl … (inr … start_nop)): Rmcr_step_true alpha sep, Rmcr_step_false alpha sep].  
#alpha #sep 
  @(acc_sem_if_app … 
     (sem_test_char …) (sem_seq …(sem_swap_l …) (sem_move_r …)) (sem_nop …))
  [#intape #outtape #tapea whd in ⊢ (%→%→%); * * #c *
   #Hcur cases (current_to_midtape … Hcur) #ls * #rs #Hintape
   #csep #Htapea * #tapeb * #Hswap #Hmove @(ex_intro … c) %
    [@(\Pf (injective_notb ? false csep))]
   generalize in match Hintape; -Hintape cases ls
    [#Hintape %2 @(ex_intro …rs) % //
     >Htapea in Hswap; >Hintape
     whd in ⊢ (%→?); * #Hswap #_ >(Hswap … (refl …)) in Hmove;
     whd in ⊢ (%→?); * #Hmove #_ >Hmove //
    |#a #ls1 #Hintape %1
     @(ex_intro … a) @(ex_intro … ls1) @(ex_intro … rs) % //
     @(proj2 … Hmove) @(proj2 … Hswap) >Htapea //
    ]
  |#intape #outtape #tapea whd in ⊢ (%→%→%);
   cases (current alpha intape) 
    [#_ #_ #_ * #Hfalse @False_ind @Hfalse %
    |#c * #H1 #H2 #Htapea #_ #_ % // lapply (H1 c (refl …)) #csep 
     lapply (injective_notb ? true csep) -csep #csep >(\P csep) //
    ]   
  ]
qed.

(* the move_char (variant c) machine *)
definition move_char_r ≝ 
  λalpha,sep.whileTM alpha (mcr_step alpha sep) (inr … (inl … (inr … start_nop))).

definition R_move_char_r ≝ 
  λalpha,sep,t1,t2.
    ∀b,a,ls,rs. t1 = midtape alpha (a::ls) b rs → 
    (b = sep → t2 = t1) ∧
    (∀rs1,rs2.rs = rs1@sep::rs2 → 
     b ≠ sep → memb ? sep rs1 = false → 
     t2 = midtape alpha (a::reverse ? rs1@b::ls) sep rs2).

lemma sem_move_char_r :
  ∀alpha,sep.
  WRealize alpha (move_char_r alpha sep) (R_move_char_r alpha sep).
#alpha #sep #inc #i #outc #Hloop
lapply (sem_while … (sem_mcr_step alpha sep) inc i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ whd in ⊢ (% → ?); #H1 #b #a #ls #rs #Htapea
  %
  [ #Hb >Htapea in H1; >Hb #H1 cases (H1 ??)
    [#_ #H2 >H2 % |*: % #H2 normalize in H2; destruct (H2)]
  | #rs1 #rs2 #Hrs #Hb #Hrs1 
    >Htapea in H1; #H1 cases (H1 ??)
    [#Hfalse @False_ind @(absurd ?? Hb) normalize in Hfalse; destruct %
    |*:% #H2 normalize in H2; destruct (H2) ]
  ]
| #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH -HRfalse whd in ⊢ (%→%); #IH
  #b0 #a0 #ls #rs #Htapea cases Hstar1 #b * #bsep *
  [* #a * #ls1 * #rs1 * >Htapea #H destruct (H) #Htapeb %
    [#Hb @False_ind /2/
    |* (* by cases on rs1 *)
      [#rs2 whd in ⊢ (???%→?); #Hrs #_ #_ (* normalize *)
       >Hrs in Htapeb; #Htapeb normalize in Htapeb;
       cases (IH … Htapeb) #Houtc #_ >Houtc normalize // 
     |#r0 #rs0 #rs2 #Hrs #_ #Hrs0
      cut (r0 ≠ sep ∧ memb … sep rs0 = false)
       [%
         [% #Hr0 >Hr0 in Hrs0; >memb_hd #Hfalse destruct
         |whd in Hrs0:(??%?); cases (sep==r0) in Hrs0; normalize #Hfalse
           [ destruct | @Hfalse ]]
         ] *
      #Hr0 -Hrs0 #Hrs0 >Hrs in Htapeb;
      normalize in ⊢ (%→?); #Htapeb
      cases (IH … Htapeb) -IH #_ #IH 
      >reverse_cons >associative_append @IH //
     ]
   ]
 |* #rs1 * >Htapea #H destruct (H)
 ]
qed.

lemma WF_mcr_niltape:
  ∀alpha,sep. WF ? (inv ? (Rmcr_step_true alpha sep)) (niltape alpha).
#alpha #sep @wf #t1 whd in ⊢ (%→?); * #b * #_ * 
  [* #a * #ls * #rs * #H destruct | * #rs * #H destruct ]
qed.

lemma WF_mcr_rightof:
  ∀alpha,sep,a,ls. WF ? (inv ? (Rmcr_step_true alpha sep)) (rightof alpha a ls).
#alpha #sep #a #ls @wf #t1 whd in ⊢ (%→?); * #b * #_ * 
  [* #a * #ls * #rs * #H destruct | * #rs * #H destruct ]
qed.

lemma WF_mcr_leftof:
  ∀alpha,sep,a,rs. WF ? (inv ? (Rmcr_step_true alpha sep)) (leftof alpha a rs).
#alpha #sep #a #rs @wf #t1 whd in ⊢ (%→?); * #b * #_ * 
  [* #a * #ls * #rs * #H destruct | * #rs * #H destruct ]
qed.

lemma terminate_move_char_r :
  ∀alpha,sep.∀t. Terminate alpha (move_char_r alpha sep) t.
#alpha #sep #t @(terminate_while … (sem_mcr_step alpha sep)) [%]
cases t // #ls #c #rs generalize in match ls; generalize in match c; elim rs 
  [#c1 #l1 @wf #t1 whd in ⊢ (%→?); * #b * #bsep *
    [* #a * #ls1 * #rs1 * #H destruct #Ht1 >Ht1 //
    |* #rs1 * #_ #Ht1 >Ht1 //
    ]
  |#a #ls1 #Hind #c1 #l1 @wf #t1 whd in ⊢ (%→?); * #b * #bsep *
    [* #a * #ls1 * #rs1 * #H destruct whd in ⊢ ((???%)→?); #Ht1 >Ht1 @Hind
    |* #rs1 * #_ #Ht1 >Ht1 //
    ]
qed.

lemma ssem_move_char_r :
  ∀alpha,sep.
  Realize alpha (move_char_r alpha sep) (R_move_char_r alpha sep).
/2/ qed.


(******************************* move_char_l **********************************)
(* MOVE_CHAR (left) MACHINE

Sposta il carattere binario su cui si trova la testina appena prima del primo # 
alla sua sinistra.

Input:
(ls,cs,rs can be empty; # is a parameter)

  ls # cs x rs
        ^
Output:
  ls # x cs rs
       ^
Initial state = 〈0,#〉
Final state = 〈4,#〉

*)

definition mcl_step ≝ λalpha:FinSet.λsep:alpha.
  ifTM alpha (test_char ? (λc.¬c==sep))
     (single_finalTM … (swap_r alpha sep · move_l ?)) (nop ?) tc_true.

definition Rmcl_step_true ≝ 
  λalpha,sep,t1,t2. 
   ∃b. b ≠ sep ∧
    ((∃a,ls,rs.
       t1 = midtape alpha ls b (a::rs) ∧
       t2 = mk_tape alpha (tail ? ls) (option_hd ? ls) (a::b::rs)) ∨
     (∃ls.
       t1 = midtape alpha ls b [ ] ∧
       t2 = rightof alpha b ls)).
       
definition Rmcl_step_false ≝ 
  λalpha,sep,t1,t2.
    right ? t1 ≠ [] →  current alpha t1 ≠ None alpha → 
      current alpha t1 = Some alpha sep ∧ t2 = t1.
      
definition mcls_acc: ∀alpha:FinSet.∀sep:alpha.states ? (mcl_step alpha sep)
 ≝ λalpha,sep.inr … (inl … (inr … start_nop)).

lemma sem_mcl_step :
  ∀alpha,sep.
  mcl_step alpha sep ⊨ 
    [mcls_acc ??: Rmcl_step_true alpha sep, Rmcl_step_false alpha sep].  
#alpha #sep 
  @(acc_sem_if_app … 
     (sem_test_char …) (sem_seq …(sem_swap_r …) (sem_move_l …)) (sem_nop …))
  [#intape #outtape #tapea whd in ⊢ (%→%→%); * * #c *
   #Hcur cases (current_to_midtape … Hcur) #ls * #rs #Hintape
   #csep #Htapea * #tapeb * #Hswap #Hmove @(ex_intro … c) %
    [@(\Pf (injective_notb ? false csep))]
   generalize in match Hintape; -Hintape cases rs
    [#Hintape %2 @(ex_intro …ls) % //
     >Htapea in Hswap; >Hintape
     whd in ⊢ (%→?); * #Hswap #_ >(Hswap … (refl …)) in Hmove;
     whd in ⊢ (%→?); * #Hmove #_ >Hmove //
    |#a #rs1 #Hintape %1
     @(ex_intro … a) @(ex_intro … ls) @(ex_intro … rs1) % //
     @(proj2 … Hmove) @(proj2 … Hswap) >Htapea //
    ]
  |#intape #outtape #tapea whd in ⊢ (%→%→%);
   cases (current alpha intape) 
    [#_ #_ #_ * #Hfalse @False_ind @Hfalse %
    |#c * #H1 #H2 #Htapea #_ #_ % // lapply (H1 c (refl …)) #csep 
     lapply (injective_notb ? true csep) -csep #csep >(\P csep) //
    ]   
  ]
qed.

definition move_char_l ≝ 
  λalpha,sep.whileTM alpha (mcl_step alpha sep) (inr … (inl … (inr … start_nop))).

definition R_move_char_l ≝ 
  λalpha,sep,t1,t2.
    ∀b,a,ls,rs. t1 = midtape alpha ls b (a::rs) → 
    (b = sep → t2 = t1) ∧
    (∀ls1,ls2.ls = ls1@sep::ls2 → 
     b ≠ sep → memb ? sep ls1 = false → 
     t2 = midtape alpha ls2 sep (a::reverse ? ls1@b::rs)).
     
lemma sem_move_char_l :
  ∀alpha,sep.
  WRealize alpha (move_char_l alpha sep) (R_move_char_l alpha sep).
#alpha #sep #inc #i #outc #Hloop
lapply (sem_while … (sem_mcl_step alpha sep) inc i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ whd in ⊢ (% → ?); #H1 #b #a #ls #rs #Htapea
  %
  [ #Hb >Htapea in H1; >Hb #H1 cases (H1 ??)
    [#_ #H2 >H2 % |*: % #H2 normalize in H2; destruct (H2)]
  | #rs1 #rs2 #Hrs #Hb #Hrs1 
    >Htapea in H1; #H1 cases (H1 ??)
    [#Hfalse @False_ind @(absurd ?? Hb) normalize in Hfalse; destruct %
    |*:% #H2 normalize in H2; destruct (H2) ]
  ]
| #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH -HRfalse whd in ⊢ (%→%); #IH
  #b0 #a0 #ls #rs #Htapea cases Hstar1 #b * #bsep *
  [* #a * #ls1 * #rs1 * >Htapea #H destruct (H) #Htapeb %
    [#Hb @False_ind /2/
    |* (* by cases on ls1 *)
      [#rs2 whd in ⊢ (???%→?); #Hrs #_ #_ (* normalize *)
       >Hrs in Htapeb; #Htapeb normalize in Htapeb;
       cases (IH … Htapeb) #Houtc #_ >Houtc normalize // 
     |#r0 #rs0 #rs2 #Hrs #_ #Hrs0
      cut (r0 ≠ sep ∧ memb … sep rs0 = false)
       [%
         [% #Hr0 >Hr0 in Hrs0; >memb_hd #Hfalse destruct
         |whd in Hrs0:(??%?); cases (sep==r0) in Hrs0; normalize #Hfalse
           [ destruct | @Hfalse ]]
         ] *
      #Hr0 -Hrs0 #Hrs0 >Hrs in Htapeb;
      normalize in ⊢ (%→?); #Htapeb
      cases (IH … Htapeb) -IH #_ #IH 
      >reverse_cons >associative_append @IH //
     ]
   ]
 |* #rs1 * >Htapea #H destruct (H)
 ]
qed.

lemma WF_mcl_niltape:
  ∀alpha,sep. WF ? (inv ? (Rmcl_step_true alpha sep)) (niltape alpha).
#alpha #sep @wf #t1 whd in ⊢ (%→?); * #b * #_ * 
  [* #a * #ls * #rs * #H destruct | * #rs * #H destruct ]
qed.

lemma WF_mcl_rightof:
  ∀alpha,sep,a,ls. WF ? (inv ? (Rmcl_step_true alpha sep)) (rightof alpha a ls).
#alpha #sep #a #ls @wf #t1 whd in ⊢ (%→?); * #b * #_ * 
  [* #a * #ls * #rs * #H destruct | * #rs * #H destruct ]
qed.

lemma WF_mcl_leftof:
  ∀alpha,sep,a,rs. WF ? (inv ? (Rmcl_step_true alpha sep)) (leftof alpha a rs).
#alpha #sep #a #rs @wf #t1 whd in ⊢ (%→?); * #b * #_ * 
  [* #a * #ls * #rs * #H destruct | * #rs * #H destruct ]
qed.

lemma terminate_move_char_l :
  ∀alpha,sep.∀t. Terminate alpha (move_char_l alpha sep) t.
#alpha #sep #t @(terminate_while … (sem_mcl_step alpha sep)) [%]
cases t // #ls elim ls 
  [#c1 #l1 @wf #t1 whd in ⊢ (%→?); * #b * #bsep *
    [* #a * #ls1 * #rs1 * #H destruct #Ht1 >Ht1 //
    |* #rs1 * #_ #Ht1 >Ht1 //
    ]
  |#a #ls1 #Hind #c1 #l1 @wf #t1 whd in ⊢ (%→?); * #b * #bsep *
    [* #a * #ls1 * #rs1 * #H destruct whd in ⊢ ((???%)→?); #Ht1 >Ht1 @Hind
    |* #rs1 * #_ #Ht1 >Ht1 //
    ]
qed.

lemma ssem_move_char_l:
  ∀alpha,sep.
  Realize alpha (move_char_l alpha sep) (R_move_char_l alpha sep).
/2/ qed.
   
