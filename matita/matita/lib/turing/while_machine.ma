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

include "basics/star.ma".
include "turing/mono.ma".

(* The following machine implements a while-loop over a body machine $M$. 
We just need to extend $M$ adding a single transition leading back from a 
distinguished final state $q$ to the initial state. *)

definition while_trans ≝ λsig. λM : TM sig. λq:states sig M. λp.
  let 〈s,a〉 ≝ p in
  if s == q then 〈start ? M, None ?,N〉
  else trans ? M p.
  
definition whileTM ≝ λsig. λM : TM sig. λqacc: states ? M.
  mk_TM sig 
    (states ? M)
    (while_trans sig M qacc)
    (start sig M)
    (λs.halt sig M s ∧ ¬ s==qacc).

lemma while_trans_false : ∀sig,M,q,p.
  \fst p ≠ q → trans sig (whileTM sig M q) p = trans sig M p.
#sig #M #q * #q1 #a #Hq normalize >(\bf Hq) normalize //
qed.

lemma loop_lift_acc : ∀A,B,k,lift,f,g,h,hlift,c1,c2,subh.
  (∀x.subh x = true → h x = true) →
  (∀x.subh x = false → hlift (lift x) = h x) → 
  (∀x.h x = false → lift (f x) = g (lift x)) →
  subh c2 = false →
  loop A k f h c1 = Some ? c2 → 
  loop B k g hlift (lift c1) = Some ? (lift … c2).
#A #B #k #lift #f #g #h #hlift #c1 #c2 #subh #Hsubh #Hlift #Hfg #Hc2
generalize in match c1; elim k
[#c0 normalize in ⊢ (??%? → ?); #Hfalse destruct (Hfalse)
|#k0 #IH #c0 whd in ⊢ (??%? → ??%?);
 cases (true_or_false (h c0)) #Hc0 >Hc0 
   [ normalize #Heq destruct (Heq) >(Hlift … Hc2) >Hc0 // 
   | normalize >(Hlift c0) 
     [>Hc0 normalize <(Hfg … Hc0) @IH 
     |cases (true_or_false (subh c0)) // 
      #H <Hc0 @sym_eq >H @Hsubh //
   ]
 ]
qed.

lemma tech1: ∀A.∀R1,R2:relation A. 
  ∀a,b. (R1 ∘ ((star ? R1) ∘ R2)) a b → ((star ? R1) ∘ R2) a b.
#A #R1 #R2 #a #b #H lapply (sub_assoc_l ?????? H) @sub_comp_l -a -b 
#a #b * #c * /2/ 
qed.

lemma halt_while_acc : 
  ∀sig,M,acc.halt sig (whileTM sig M acc) acc = false.
#sig #M #acc normalize >(\b ?) // cases (halt sig M acc) %
qed.

lemma halt_while_not_acc : 
  ∀sig,M,acc,s.s == acc = false → halt sig (whileTM sig M acc) s = halt sig M s.
#sig #M #acc #s #neqs normalize >neqs cases (halt sig M s) %
qed.

lemma step_while_acc :
 ∀sig,M,acc,c.cstate ?? c = acc → 
   step sig (whileTM sig M acc) c = initc … (ctape ?? c).
#sig #M #acc * #s #t #Hs normalize >(\b Hs) %
qed.

theorem sem_while: ∀sig,M,acc,Rtrue,Rfalse.
  halt sig M acc = true →
  M ⊨ [acc: Rtrue,Rfalse] → 
    whileTM sig M acc ⊫ (star ? Rtrue) ∘ Rfalse.
#sig #M #acc #Rtrue #Rfalse #Hacctrue #HaccR #t #i
generalize in match t;
@(nat_elim1 … i) #m #Hind #intape #outc #Hloop
cases (loop_split ?? (λc. halt sig M (cstate ?? c)) ????? Hloop)
  [#k1 * #outc1 * #Hloop1 #Hloop2
   cases (HaccR intape) #k * #outcM * * #HloopM #HMtrue #HMfalse
   cut (outcM = outc1)
   [ @(loop_eq … k … Hloop1) 
     @(loop_lift ?? k (λc.c) ? 
                (step ? (whileTM ? M acc)) ? 
                (λc.halt sig M (cstate ?? c)) ?? 
                ?? HloopM)
     [ #x %
     | * #s #t #Hx whd in ⊢ (??%%); >while_trans_false
       [%
       |% #Hfalse <Hfalse in Hacctrue; >Hx #H0 destruct ]
     ]
  | #HoutcM1 cases (true_or_false (cstate ?? outc1 == acc)) #Hacc
      [@tech1 @(ex_intro … (ctape ?? outc1)) %
        [ <HoutcM1 @HMtrue >HoutcM1 @(\P Hacc)
        |@(Hind (m-k1)) 
          [ cases m in Hloop;
            [normalize #H destruct (H) ]
             #m' #_ cases k1 in Hloop1;
             [normalize #H destruct (H) ]
             #k1' #_ normalize /2/
           | <Hloop2 whd in ⊢ (???%);
             >(\P Hacc) >halt_while_acc whd in ⊢ (???%);
             normalize in match (halt ?? acc);
             >step_while_acc // @(\P Hacc)
           ]
         ]
      |@(ex_intro … intape) % //
       cut (Some ? outc1 = Some ? outc)
       [ <Hloop1 <Hloop2 >loop_p_true in ⊢ (???%); //
         normalize >(loop_Some ?????? Hloop1) >Hacc %
       | #Houtc1c destruct @HMfalse @(\Pf Hacc)
       ]
     ]
   ]
 | * #s0 #t0 normalize cases (s0 == acc) normalize
   [ cases (halt sig M s0) normalize #Hfalse destruct
   | cases (halt sig M s0) normalize //
   ]
 ]
qed.

theorem terminate_while: ∀sig,M,acc,Rtrue,Rfalse,t.
  halt sig M acc = true →
  M ⊨ [acc: Rtrue,Rfalse] → 
  WF ? (inv … Rtrue) t → whileTM sig M acc ↓ t.
#sig #M #acc #Rtrue #Rfalse #t #Hacctrue #HM #HWF elim HWF
#t1 #H #Hind cases (HM … t1) #i * #outc * * #Hloop
#Htrue #Hfalse cases (true_or_false (cstate … outc == acc)) #Hcase
  [cases (Hind ? (Htrue … (\P Hcase))) #iwhile * #outcfinal
   #Hloopwhile @(ex_intro … (i+iwhile)) 
   @(ex_intro … outcfinal) @(loop_merge … outc … Hloopwhile)
    [@(λc.halt sig M (cstate … c))
    |* #s0 #t0 normalize cases (s0 == acc) normalize
     [ cases (halt sig M s0) // 
     | cases (halt sig M s0) normalize //
     ]
    |@(loop_lift ?? i (λc.c) ? 
                (step ? (whileTM ? M acc)) ? 
                (λc.halt sig M (cstate ?? c)) ?? 
                ?? Hloop)
     [ #x %
     | * #s #t #Hx whd in ⊢ (??%%); >while_trans_false
       [%
       |% #Hfalse <Hfalse in Hacctrue; >Hx #H0 destruct ]
     ]
   |@step_while_acc @(\P Hcase)
   |>(\P Hcase) @halt_while_acc
   ]
 |@(ex_intro … i) @(ex_intro … outc)
  @(loop_lift_acc ?? i (λc.c) ?????? (λc.cstate ?? c == acc) ???? Hloop)
   [#x #Hx >(\P Hx) //
   |#x @halt_while_not_acc
   |#x #H whd in ⊢ (??%%); >while_trans_false [%]
    % #eqx >eqx in H; >Hacctrue #H destruct
   |@Hcase
   ]
 ]
qed.

theorem terminate_while_guarded: ∀sig,M,acc,Pre,Rtrue,Rfalse.
  halt sig M acc = true →
  accGRealize sig M acc Pre Rtrue Rfalse → 
  (∀t1,t2. Pre t1 → Rtrue t1 t2 → Pre t2) → ∀t.
  WF ? (inv … Rtrue) t → Pre t → whileTM sig M acc ↓ t.
#sig #M #acc #Pre #Rtrue #Rfalse #Hacctrue #HM #Hinv #t #HWF elim HWF
#t1 #H #Hind #HPre cases (HM … t1 HPre) #i * #outc * * #Hloop
#Htrue #Hfalse cases (true_or_false (cstate … outc == acc)) #Hcase
  [cases (Hind ? (Htrue … (\P Hcase)) ?) 
    [2: @(Hinv … HPre) @Htrue @(\P Hcase)]
   #iwhile * #outcfinal
   #Hloopwhile @(ex_intro … (i+iwhile)) 
   @(ex_intro … outcfinal) @(loop_merge … outc … Hloopwhile)
    [@(λc.halt sig M (cstate … c))
    |* #s0 #t0 normalize cases (s0 == acc) normalize
     [ cases (halt sig M s0) // 
     | cases (halt sig M s0) normalize //
     ]
    |@(loop_lift ?? i (λc.c) ? 
                (step ? (whileTM ? M acc)) ? 
                (λc.halt sig M (cstate ?? c)) ?? 
                ?? Hloop)
     [ #x %
     | * #s #t #Hx whd in ⊢ (??%%); >while_trans_false
       [%
       |% #Hfalse <Hfalse in Hacctrue; >Hx #H0 destruct ]
     ]
   |@step_while_acc @(\P Hcase)
   |>(\P Hcase) @halt_while_acc
   ]
 |@(ex_intro … i) @(ex_intro … outc)
  @(loop_lift_acc ?? i (λc.c) ?????? (λc.cstate ?? c == acc) ???? Hloop)
   [#x #Hx >(\P Hx) //
   |#x @halt_while_not_acc
   |#x #H whd in ⊢ (??%%); >while_trans_false [%]
    % #eqx >eqx in H; >Hacctrue #H destruct
   |@Hcase
   ]
 ]
qed.
 