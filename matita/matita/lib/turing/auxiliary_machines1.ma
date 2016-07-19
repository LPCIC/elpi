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

(* move until test *)
definition mut_step ≝ λalpha,D,test.
ifTM ? (test_char alpha test) (single_finalTM ? (move alpha D)) (nop ?) tc_true.
 
definition R_mut_step_true ≝ λalpha,D,test,t1,t2.
  ∃ls,c,rs.
    t1 = midtape alpha ls c rs ∧ test c = true ∧ t2 = tape_move ? t1 D.

definition R_mut_step_false ≝ λalpha,test.λt1,t2:tape alpha.
  (∀ls,c,rs.t1 = midtape alpha ls c rs → test c = false) 
  ∧ t2 = t1.

definition mut_acc : ∀alpha,D,test.states ? (mut_step alpha D test) ≝ 
λalpha,D,test.(inr … (inl … (inr … start_nop))).
  
lemma sem_mut_step :
  ∀alpha,D,test.mut_step alpha D test ⊨ 
   [ mut_acc … : R_mut_step_true alpha D test, R_mut_step_false alpha test] .
#alpha #D #tets #ta
@(acc_sem_if_app ??????????? (sem_test_char …) 
  (sem_move_single …) (sem_nop alpha) ??)
  [#tb #tc #td * * #c * #Hcurtb #Htrue
   cases (current_to_midtape … Hcurtb) #ls * #rs #Hmidtb 
   #tbtd #Hmove %{ls} %{c} %{rs} % // % // 
  |#tb #tc #td * #Hcurtb #Htb whd in ⊢ (%→?); #Htc whd % //
   lapply (refl ? (current ? tb)) cases (current ? tb) in ⊢ (???%→?);
    [#H #ls #c #rs #Htb >Htb in H; normalize #HF destruct (HF)
    |#c #H #ls #c0 #rs #Htb @Hcurtb >Htb //  
    ]
  ]
qed.

definition move_until ≝ λsig,D,test.
  whileTM sig (mut_step sig D test) (mut_acc …).

definition R_move_l_until ≝ 
  λsig,test,t1,t2.
  (current ? t1 = None ? → t2 = t1) ∧
  ∀ls,a,rs.t1 = midtape sig ls a rs → 
    (test a = false ∧ t2 = t1) ∨
    ((∃ls1,b,ls2.
       ls = ls1@b::ls2 ∧ 
       test b = false ∧
        (∀x. mem ? x (a::ls1) → test x = true) ∧
        t2 = midtape ? ls2 b ((reverse ? (a::ls1))@rs)) ∨
      (∃b,lss. 
        (∀x. mem ? x (a::ls) → test x = true) ∧
        a::ls = lss@[b] ∧
        t2 = leftof ? b ((reverse ? lss)@rs))).  
  
lemma sem_move_L_until:
  ∀sig,test.
  WRealize sig (move_until sig L test) (R_move_l_until sig test).
#sig #test #inc #j #outc #Hloop
lapply (sem_while … (sem_mut_step sig L test) inc j outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ whd in ⊢ (% → ?); * #H1 #H2 % 
  [#Htape1 @H2
  |#ls #a #rs #Htapea % % [@(H1 … Htapea) |@H2]
  ]
| #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH -HRfalse whd in ⊢ (%→%); 
  * #IH1 #IH2 %
  [#Htapeb cases Hstar1 #ls * #b * #rs * *
   #H1 >H1 in Htapeb; whd in ⊢ (??%?→?); #H destruct (H)
  |#ls #b0 #rs #Htapeb cases Hstar1 
   #ls1 * #b * #rs1 * * >Htapeb #H destruct (H) 
   #Hb cases ls1 
    [whd in ⊢ (???%→?); #Htapec >Htapec in IH1; #IH1
     %2 %2 %{b} %{[ ]} % [% [#x * [//|@False_ind] | //] |@IH1 //]
    |#a #ls2 whd in ⊢ (???%→?); #Htapec 
     %2 cases (IH2 … Htapec)
      [* #afalse #Hout %1
       %{[ ]} %{a} %{ls2} 
       %[%[%[//|//] |#x * [#eqxa >eqxa // |@False_ind]]
        |>Hout >reverse_single @Htapec
        ]
      |*
        [-IH1 -IH2 #IH  
         %1 cases IH -IH #ls3 * #b0 * #ls4 * * * #H1 #H2 #H3 #H4
         %{(a::ls3)} %{b0} %{ls4} 
         %[%[%[>H1 //|//]| #x * [#eqxb >eqxb //|@H3]]
          |>H4 >reverse_cons in ⊢ (???%); >associative_append //
          ]
        |-IH1 -IH2 #IH  
         %2 cases IH -IH #b0 * #ls3 * * #H1 #H2 #H3 
         %{b0} %{(b::ls3)} 
         %[%[#x * [#eqxb >eqxb //|@H1]|>H2 //]
          |>H3 >reverse_cons in ⊢ (???%); >associative_append //
          ]
        ]
      ]
    ]
  ]
qed.

definition R_move_R_until ≝ 
  λsig,test,t1,t2.
  (current ? t1 = None ? → t2 = t1) ∧
  ∀ls,a,rs.t1 = midtape sig ls a rs → 
    (test a = false ∧ t2 = t1) ∨
    ((∃rs1,b,rs2.
       rs = rs1@b::rs2 ∧ 
       test b = false ∧
        (∀x. mem ? x (a::rs1) → test x = true) ∧
        t2 = midtape ? ((reverse ? (a::rs1))@ls) b rs2) ∨
      (∃b,rss. 
        (∀x. mem ? x (a::rs) → test x = true) ∧
        a::rs = rss@[b] ∧
        t2 = rightof ? b ((reverse ? rss)@ls))).  
        
lemma sem_move_R_until:
  ∀sig,test.
  WRealize sig (move_until sig R test) (R_move_R_until sig test).
#sig #test #inc #j #outc #Hloop
lapply (sem_while … (sem_mut_step sig R test) inc j outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ whd in ⊢ (% → ?); * #H1 #H2 % 
  [#Htape1 @H2
  |#ls #a #rs #Htapea % % [@(H1 … Htapea) |@H2]
  ]
| #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH -HRfalse whd in ⊢ (%→%); 
  * #IH1 #IH2 %
  [#Htapeb cases Hstar1 #ls * #b * #rs * *
   #H1 >H1 in Htapeb; whd in ⊢ (??%?→?); #H destruct (H)
  |#ls #b0 #rs #Htapeb cases Hstar1 
   #ls1 * #b * #rs1 * * >Htapeb #H destruct (H) 
   #Hb cases rs1 
    [whd in ⊢ (???%→?); #Htapec >Htapec in IH1; #IH1
     %2 %2 %{b} %{[ ]} % [% [#x * [//|@False_ind] | //] |@IH1 //]
    |#a #rs2 whd in ⊢ (???%→?); #Htapec 
     %2 cases (IH2 … Htapec)
      [* #afalse #Hout %1
       %{[ ]} %{a} %{rs2} 
       %[%[%[//|//] |#x * [#eqxa >eqxa // |@False_ind]]
        |>Hout >reverse_single @Htapec
        ]
      |*
        [-IH1 -IH2 #IH  
         %1 cases IH -IH #rs3 * #b0 * #rs4 * * * #H1 #H2 #H3 #H4
         %{(a::rs3)} %{b0} %{rs4} 
         %[%[%[>H1 //|//]| #x * [#eqxb >eqxb //|@H3]]
          |>H4 >reverse_cons in ⊢ (???%); >associative_append //
          ]
        |-IH1 -IH2 #IH  
         %2 cases IH -IH #b0 * #rs3 * * #H1 #H2 #H3 
         %{b0} %{(b::rs3)} 
         %[%[#x * [#eqxb >eqxb //|@H1]|>H2 //]
          |>H3 >reverse_cons in ⊢ (???%); >associative_append //
          ]
        ]
      ]
    ]
  ]
qed.

(* termination *)

lemma WF_mut_niltape:
  ∀alpha,D,test. WF ? (inv ? (R_mut_step_true alpha D test)) (niltape alpha).
#alpha #D #test @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * * #H destruct
qed.

lemma WF_mut_rightof:
  ∀alpha,D,test,a,ls. WF ? (inv ? (R_mut_step_true alpha D test)) (rightof alpha a ls).
#alpha #D #test #a #ls @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * * #H destruct
qed.

lemma WF_mut_leftof:
  ∀alpha,D,test,a,rs. WF ? (inv ? (R_mut_step_true alpha D test)) (leftof alpha a rs).
#alpha #D #test #a #rs @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * * #H destruct  
qed.

lemma terminate_move_until_L:
  ∀alpha,test.∀t. Terminate alpha (move_until alpha L test) t.
#alpha #test #t @(terminate_while … (sem_mut_step alpha L test)) [%]
cases t // #ls elim ls 
  [#c1 #l1 @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * *
   #_ #_ #Ht1 >Ht1 //
  |#a #ls1 #Hind #c1 #l1 @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * *
   #_ #_ #Ht1 >Ht1 //
  ]
qed.

lemma terminate_move_until_R:
  ∀alpha,test.∀t. Terminate alpha (move_until alpha R test) t.
#alpha #test #t @(terminate_while … (sem_mut_step alpha R test)) [%]
cases t // #ls #c #rs lapply c -c lapply ls -ls elim rs 
  [#c1 #l1 @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * *
   #_ #_ #Ht1 >Ht1 //
  |#a #ls1 #Hind #c1 #l1 @wf #t1 whd in ⊢ (%→?); * #ls * #b * #rs * *
   #_ #_ #Ht1 >Ht1 //
  ]
qed.

lemma ssem_move_until_L :
  ∀alpha,test.
  Realize alpha (move_until alpha L test) (R_move_l_until alpha test).
/2/ qed.

lemma ssem_move_until_R :
  ∀alpha,test.
  Realize alpha (move_until alpha R test) (R_move_R_until alpha test).
/2/ qed.

(*********************************** extend ***********************************)
(* if current = Null write a character a. Used to dynamically extend the tape *)  

definition extend ≝ λalpha,a.
  ifTM ? (test_null alpha) (nop ?) (write alpha a) tc_true.
 
definition R_extend ≝ λalpha,a,t1,t2.
  (current ? t1 = None ? → t2 = midtape alpha (left ? t1) a (right ? t1)) ∧
  (current ? t1 ≠ None ? → t2 = t1).
  
lemma sem_extend : ∀alpha,a.
  extend alpha a ⊨ R_extend alpha a.
#alpha #a #ta
@(sem_if_app … (sem_test_null …) (sem_nop … ) (sem_write_strong …) ??)
-ta #t1 #t2 #t3 *
  [* * #H1 #H2 #H3 % 
    [#Hcur >Hcur in H1; * #H @False_ind @H //|#_ >H2 @H3]
  |* * #H1 #H2 #H3 %
    [#_ >H2 @H3 | >H1 * #H @False_ind @H //]
  ]
qed.

(********************************** extend1 ***********************************)
(* a slightly different version: we add a to the left of the current position *)

definition extendL ≝ λalpha,a.
  (move_l alpha) · (write alpha a) · (move_r alpha).

definition R_extendL ≝ λalpha,a,t1,t2.
  (∀b,ls. t1 = leftof ? b ls → t2 = midtape alpha [a] b ls) ∧
  (∀b,ls,rs. t1 = midtape ? ls b rs → t2 = midtape alpha (a::(tail ? ls)) b rs).
 
lemma sem_extendL : ∀alpha,a.
  extendL alpha a ⊨ R_extendL alpha a.
#alpha #a 
@(sem_seq_app … (sem_move_l …) 
  (sem_seq … (sem_write_strong … ) (sem_move_r …) …))
#tin #tout * #t1 * * #Ht1a #Ht1b * #t2 * #Ht2 * #_ #Ht3 %
  [#b #ls #Htin >Htin in Ht1a; #Ht1 <(Ht1 … (refl … )) in Ht2;
   normalize in ⊢ (%→?); #Ht2 @(Ht3 … Ht2)
  |#b #ls #rs #Htin lapply (Ht1b … Htin) #Ht1 >Ht1 in Ht2;
   #Ht2 lapply(Ht3 ??? Ht2) cases ls normalize //
  ]
qed.
