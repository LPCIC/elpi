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

include "turing/turing.ma".

(**************************** single final machine ****************************)

definition single_finalTM ≝ 
  λsig,n.λM:mTM sig n.seq ?? M (nop ??).

lemma sem_single_final: ∀sig,n.∀M: mTM sig n.∀R.
  M ⊨ R → single_finalTM sig n M ⊨ R.
#sig #n #M #R #HR #intape 
cases (sem_seq ?????? HR (sem_nop …) intape)
#k * #outc * #Hloop * #ta * #Hta whd in ⊢ (%→?); #Houtc
@(ex_intro ?? k) @(ex_intro ?? outc) %  [ @Hloop | >Houtc // ]
qed.

lemma single_final: ∀sig,n.∀M: mTM sig n.∀q1,q2.
  halt ?? (single_finalTM sig n M) q1 = true 
    →  halt ?? (single_finalTM sig n M) q2 = true → q1=q2.
#sig #n #M * 
  [#q1M #q2 whd in match (halt ????); #H destruct
  |#q1nop *
    [#q2M #_ whd in match (halt ????); #H destruct
    |#q2nop #_ #_ @eq_f normalize @nop_single_state
    ]
  ]
qed.
  
(******************************** if machine **********************************)

definition if_trans ≝ λsig,n. λM1,M2,M3 : mTM sig n. λq:states sig n M1.
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig n M1 s1 then
        if s1==q then 〈inr … (inl … (start sig n M2)), null_action ??〉
        else 〈inr … (inr … (start sig n M3)), null_action ??〉
      else let 〈news1,m〉 ≝ trans sig n M1 〈s1,a〉 in
       〈inl … news1,m〉
  | inr s' ⇒ 
      match s' with
      [ inl s2 ⇒ let 〈news2,m〉 ≝ trans sig n M2 〈s2,a〉 in
         〈inr … (inl … news2),m〉
      | inr s3 ⇒ let 〈news3,m〉 ≝ trans sig n M3 〈s3,a〉 in
         〈inr … (inr … news3),m〉
      ]
  ]. 
 
definition ifTM ≝ λsig,n. λcondM,thenM,elseM : mTM sig n.
  λqacc: states sig n condM.
  mk_mTM sig n
    (FinSum (states sig n condM) (FinSum (states sig n thenM) (states sig n elseM)))
    (if_trans sig n condM thenM elseM qacc)
    (inl … (start sig n condM))
    (λs.match s with
      [ inl _ ⇒ false 
      | inr s' ⇒ match s' with 
        [ inl s2 ⇒ halt sig n thenM s2
        | inr s3 ⇒ halt sig n elseM s3 ]]).

(****************************** lifting lemmas ********************************)
lemma trans_if_liftM1 : ∀sig,n,M1,M2,M3,acc,s,a,news,move.
  halt ?? M1 s = false → 
  trans sig n M1 〈s,a〉 = 〈news,move〉 → 
  trans sig n (ifTM sig n M1 M2 M3 acc) 〈inl … s,a〉 = 〈inl … news,move〉.
#sig #n * #Q1 #T1 #init1 #halt1 #M2 #M3 #acc #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_if_liftM2 : ∀sig,n,M1,M2,M3,acc,s,a,news,move.
  halt ?? M2 s = false → 
  trans sig n M2 〈s,a〉 = 〈news,move〉 → 
  trans sig n (ifTM sig n M1 M2 M3 acc) 〈inr … (inl … s),a〉 = 〈inr… (inl … news),move〉.
#sig #n #M1 * #Q2 #T2 #init2 #halt2 #M3 #acc #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_if_liftM3 : ∀sig,n,M1,M2,M3,acc,s,a,news,move.
  halt ?? M3 s = false → 
  trans sig n M3 〈s,a〉 = 〈news,move〉 → 
  trans sig n (ifTM sig n M1 M2 M3 acc) 〈inr … (inr … s),a〉 = 〈inr… (inr … news),move〉.
#sig #n #M1 * #Q2 #T2 #init2 #halt2 #M3 #acc #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma step_if_liftM1 : ∀sig,n,M1,M2,M3,acc,c0.
 halt ?? M1 (cstate ??? c0) = false → 
 step sig n (ifTM sig n M1 M2 M3 acc) (lift_confL sig n (states ?? M1) ? c0) =
 lift_confL sig n (states ?? M1) ? (step sig n M1 c0).
#sig #n #M1 #M2 #M3 #acc * #s #t
  lapply (refl ? (trans ??? 〈s,current_chars sig n t〉))
  cases (trans ??? 〈s,current_chars sig n t〉) in ⊢ (???% → %);
  #s0 #m0 #Heq #Hhalt
  whd in ⊢ (???(?????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(????%)?); whd in ⊢ (??%?); >(trans_if_liftM1 … Hhalt Heq) //
qed.

lemma step_if_liftM2 : ∀sig,n,M1,M2,M3,acc,c0.
 halt ?? M2 (cstate ??? c0) = false → 
 step sig n (ifTM sig n M1 M2 M3 acc) (lift_confR sig ??? (lift_confL sig ??? c0)) =
 lift_confR sig ??? (lift_confL sig ??? (step sig n M2 c0)).
#sig #n #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 #M3 #acc * #s #t
  lapply (refl ? (trans ??? 〈s,current_chars sig n t〉))
  cases (trans ??? 〈s,current_chars sig n t〉) in ⊢ (???% → %);
  #s0 #m0 #Heq #Hhalt
  whd in match (step ?? M2 ?); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(????%)?); whd in ⊢ (??%?); >(trans_if_liftM2 … Hhalt Heq) //
qed.

lemma step_if_liftM3 : ∀sig,n,M1,M2,M3,acc,c0.
 halt ?? M3 (cstate ??? c0) = false → 
 step sig n (ifTM sig n M1 M2 M3 acc) (lift_confR sig ??? (lift_confR sig ??? c0)) =
 lift_confR sig ??? (lift_confR sig ??? (step sig n M3 c0)).
#sig #n #M1 #M2 #M3 #acc * #s #t
  lapply (refl ? (trans ??? 〈s,current_chars sig n t〉))
  cases (trans ??? 〈s,current_chars sig n t〉) in ⊢ (???% → %);
  #s0 #m0 #Heq #Hhalt
  whd in match (step ?? M3 ?); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(????%)?); whd in ⊢ (??%?); >(trans_if_liftM3 … Hhalt Heq) //
qed.

lemma trans_if_M1true_acc : ∀sig,n,M1,M2,M3,acc,s,a.
  halt ?? M1 s = true → s==acc = true →
  trans sig n (ifTM sig n M1 M2 M3 acc) 〈inl … s,a〉 = 
    〈inr … (inl … (start ?? M2)),null_action ??〉.
#sig #n #M1 #M2 #M3 #acc #s #a #Hhalt #Hacc whd in ⊢ (??%?); >Hhalt >Hacc %
qed.

lemma trans_if_M1true_notacc : ∀sig,n,M1,M2,M3,acc,s,a.
  halt ?? M1 s = true → s==acc = false →
  trans sig n (ifTM sig n M1 M2 M3 acc) 〈inl … s,a〉 = 
    〈inr … (inr … (start ?? M3)),null_action ??〉.
#sig #n #M1 #M2 #M3 #acc #s #a #Hhalt #Hacc whd in ⊢ (??%?); >Hhalt >Hacc %
qed.

(******************************** semantics ***********************************)
lemma sem_if: ∀sig,n.∀M1,M2,M3:mTM sig n.∀Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ [acc: Rtrue,Rfalse] → M2 ⊨ R2 → M3 ⊨ R3 → 
    ifTM sig n M1 M2 M3 acc ⊨ (Rtrue ∘ R2) ∪ (Rfalse ∘ R3).
#sig #n #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HR3 #t 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ??? outc1 == acc)) #Hacc
  [cases (HR2 (ctapes sig ?? outc1)) #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confL … outc2))) %
    [@(loop_merge ?????????
     (mk_mconfig ? (FinSum (states sig n M1) (FinSum (states sig n M2) (states sig n M3))) n
      (inr (states sig n M1) ? (inl (states sig n M2) (states sig n M3) (start sig n M2))) (ctapes ??? outc1) )
     ? 
     (loop_lift ??? 
       (lift_confL sig n (states ?? M1) (FinSum (states ?? M2) (states ?? M3)))
       (step sig n M1) (step sig n (ifTM sig n M1 M2 M3 acc)) 
       (λc.halt sig n M1 (cstate … c)) 
       (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) 
       … Hloop1))
      [* *
        [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
        | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
      |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
      |#x <p_halt_liftL %
      |whd in ⊢ (??%?); >(mconfig_expand ??? outc1)
       whd in match (lift_confL ?????);
       >(trans_if_M1true_acc … Hacc) 
        [@mconfig_eq // (* whd in ⊢ (??%?); *)
         <(tape_move_null_action sig n (ctapes sig (states sig n M1) n outc1)) in ⊢ (???%); % 
        |@(loop_Some ?????? Hloop1)]
      |cases outc1 #s1 #t1 %
      |@(loop_lift ??? 
         (λc.(lift_confR … (lift_confL sig n (states ?? M2) (states ?? M3) c)))
         … Hloop2) 
        [ * #s2 #t2 %
        | #c0 #Hhalt >(step_if_liftM2 … Hhalt) // ]
      ]
    |%1 @(ex_intro … (ctapes ??? outc1)) % 
      [@HMtrue @(\P Hacc) | >(mconfig_expand ??? outc2) @HM2 ]
    ]
  |cases (HR3 (ctapes sig ?? outc1)) #k2 * #outc2 * #Hloop2 #HM3
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confR … outc2))) %
    [@(loop_merge ?????????
     (mk_mconfig ? (FinSum (states sig ? M1) (FinSum (states sig ? M2) (states sig ? M3))) n
      (inr (states sig ? M1) ? (inr (states sig ? M2) (states sig ? M3) (start sig ? M3))) (ctapes ??? outc1) )
     ? 
     (loop_lift ??? 
       (lift_confL sig n (states ?? M1) (FinSum (states ?? M2) (states ?? M3)))
       (step sig n M1) (step sig n (ifTM sig n M1 M2 M3 acc)) 
       (λc.halt sig n M1 (cstate … c)) 
       (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) 
       … Hloop1))
      [* *
        [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
        | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
      |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
      |#x <p_halt_liftL %
      |whd in ⊢ (??%?); >(mconfig_expand ??? outc1);
       whd in match (lift_confL ?????);
       >(trans_if_M1true_notacc … Hacc) 
        [@mconfig_eq // (* whd in ⊢ (??%?); *)
         <(tape_move_null_action sig n (ctapes sig (states sig n M1) n outc1)) in ⊢ (???%); %  
        |@(loop_Some ?????? Hloop1)]
      |cases outc1 #s1 #t1 %
      |@(loop_lift ??? 
         (λc.(lift_confR … (lift_confR sig n (states ?? M2) (states ?? M3) c)))
         … Hloop2) 
        [ * #s2 #t2 %
        | #c0 #Hhalt >(step_if_liftM3 … Hhalt) // ]
      ]
    |%2 @(ex_intro … (ctapes ??? outc1)) % 
      [@HMfalse @(\Pf Hacc) | >(mconfig_expand ??? outc2) @HM3 ]
    ]
  ]
qed.

lemma sem_if_app: ∀sig,n,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,acc.
  accRealize sig n M1 acc Rtrue Rfalse  → M2 ⊨ R2  → M3 ⊨ R3 →  
    (∀t1,t2,t3. (Rtrue t1 t3 → R2 t3 t2) ∨ (Rfalse t1 t3 → R3 t3 t2) → R4 t1 t2) → 
    ifTM sig n M1 M2 M3 acc ⊨ R4.
#sig #n #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #acc
#HRacc #HRtrue #HRfalse #Hsub
#t cases (sem_if … HRacc HRtrue HRfalse t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop] cases Houtc
  [* #t3 * #Hleft #Hright @(Hsub … t3) %1 /2/
  |* #t3 * #Hleft #Hright @(Hsub … t3) %2 /2/ ]
qed.
 
(* we can probably use acc_sem_if to prove sem_if *)
(* for sure we can use acc_sem_if_guarded to prove acc_sem_if *)
lemma acc_sem_if: ∀sig,n,M1,M2,M3,Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ [acc: Rtrue, Rfalse]  → M2 ⊨ R2 → M3 ⊨ R3 → 
  ifTM sig n M1 (single_finalTM … M2) M3 acc ⊨
     [inr … (inl … (inr … start_nop)): Rtrue ∘ R2, Rfalse ∘ R3].
#sig #n #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HR3 #t 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ??? outc1 == acc)) #Hacc
  [lapply (sem_single_final … HR2) -HR2 #HR2
   cases (HR2 (ctapes sig ?? outc1)) #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) 
   @(ex_intro … (lift_confR … (lift_confL … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_mconfig ? (states sig n (ifTM sig n M1 (single_finalTM … M2) M3 acc)) n
          (inr (states sig n M1) ? (inl ? (states sig n M3) (start sig n (single_finalTM sig n M2)))) (ctapes ??? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig n (states ?? M1) (FinSum (states ?? (single_finalTM … M2)) (states ?? M3)))
          (step sig n M1) (step sig n (ifTM sig n M1 (single_finalTM ?? M2) M3 acc)) 
          (λc.halt sig n M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(mconfig_expand ??? outc1);
         whd in match (lift_confL ????);
         >(trans_if_M1true_acc … Hacc) 
          [@mconfig_eq // (* whd in ⊢ (??%?); *)
           <(tape_move_null_action sig n (ctapes sig (states sig n M1) n outc1)) in ⊢ (???%); % 
          | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confL sig n (states ?? (single_finalTM ?? M2)) (states ?? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM2 … Hhalt) // ]
        ]
      |#_ @(ex_intro … (ctapes ??? outc1)) % 
        [@HMtrue @(\P Hacc) | >(mconfig_expand ??? outc2) @HM2 ]
      ]
    |>(mconfig_expand ??? outc2) whd in match (lift_confR ?????);
     * #H @False_ind @H @eq_f @eq_f >(mconfig_expand ??? outc2)
     @single_final // @(loop_Some ?????? Hloop2)
    ]
  |cases (HR3 (ctapes sig ?? outc1)) #k2 * #outc2 * #Hloop2 #HM3
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confR … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_mconfig ? (states sig n (ifTM sig n M1 (single_finalTM … M2) M3 acc)) n
          (inr (states sig n M1) ? (inr (states sig n (single_finalTM ?? M2)) ? (start sig n M3))) (ctapes ??? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig n (states ?? M1) (FinSum (states ?? (single_finalTM … M2)) (states ?? M3)))
          (step sig n M1) (step sig n (ifTM sig n M1 (single_finalTM ?? M2) M3 acc)) 
          (λc.halt sig n M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(mconfig_expand ??? outc1);
         whd in match (lift_confL ?????);
         >(trans_if_M1true_notacc … Hacc) 
          [@mconfig_eq // (* whd in ⊢ (??%?); *)
           <(tape_move_null_action sig n (ctapes sig (states sig n M1) n outc1)) in ⊢ (???%); % 
          |@(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confR sig n (states ?? (single_finalTM ?? M2)) (states ?? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM3 … Hhalt) // ]
        ]
      |>(mconfig_expand ??? outc2) whd in match (lift_confR ?????);
       #H destruct (H) 
      ]
    |#_ @(ex_intro … (ctapes ??? outc1)) % 
      [@HMfalse @(\Pf Hacc) | >(mconfig_expand ??? outc2) @HM3 ]
    ]
  ]
qed.
    
lemma acc_sem_if_app: ∀sig,n,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,R5,acc.
  M1 ⊨ [acc: Rtrue, Rfalse] → M2 ⊨ R2 → M3 ⊨ R3 → 
    (∀t1,t2,t3. Rtrue t1 t3 → R2 t3 t2 → R4 t1 t2) → 
    (∀t1,t2,t3. Rfalse t1 t3 → R3 t3 t2 → R5 t1 t2) → 
     ifTM sig n M1 (single_finalTM … M2) M3 acc ⊨ 
       [inr … (inl … (inr … start_nop)): R4, R5].    
#sig #n #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #R5 #acc
#HRacc #HRtrue #HRfalse #Hsub1 #Hsub2 
#t cases (acc_sem_if … HRacc HRtrue HRfalse t)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.

lemma sem_single_final_guarded: ∀sig,n.∀M: mTM sig n.∀Pre,R.
  GRealize sig n M Pre R → GRealize sig n (single_finalTM sig n M) Pre R.
#sig #n #M #Pre #R #HR #intape #HPre 
cases (sem_seq_guarded ???????? HR (Realize_to_GRealize ??? (λt.True) ? (sem_nop …)) ?? HPre) //
#k * #outc * #Hloop * #ta * #Hta whd in ⊢ (%→?); #Houtc
@(ex_intro ?? k) @(ex_intro ?? outc) %  [ @Hloop | >Houtc // ]
qed.
    
lemma acc_sem_if_guarded: ∀sig,n.∀M1,M2,M3: mTM sig n.∀P,P2,Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ [acc: Rtrue, Rfalse]  → 
  (GRealize ?? M2 P2 R2) → (∀t,t0.P t → Rtrue t t0 → P2 t0) → 
  M3 ⊨ R3 → 
  accGRealize ?? (ifTM sig n M1 (single_finalTM … M2) M3 acc) 
    (inr … (inl … (inr … start_nop))) P (Rtrue ∘ R2) (Rfalse ∘ R3).
#sig #n #M1 #M2 #M3 #P #P2 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HP2 #HR3 #t #HPt 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ??? outc1 == acc)) #Hacc
  [lapply (sem_single_final_guarded … HR2) -HR2 #HR2
   cases (HR2 (ctapes sig ?? outc1) ?)
   [|@HP2 [||@HMtrue @(\P Hacc)] // ]
   #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) 
   @(ex_intro … (lift_confR … (lift_confL … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_mconfig ? (states sig n (ifTM sig n M1 (single_finalTM … M2) M3 acc)) n
          (inr (states sig n M1) ? (inl ? (states sig n M3) (start sig n (single_finalTM sig n M2)))) (ctapes ??? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig n (states ?? M1) (FinSum (states ?? (single_finalTM … M2)) (states ?? M3)))
          (step sig n M1) (step sig n (ifTM sig n M1 (single_finalTM ?? M2) M3 acc)) 
          (λc.halt sig n M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(mconfig_expand ??? outc1);
         whd in match (lift_confL ?????);
         >(trans_if_M1true_acc … Hacc) 
          [@mconfig_eq // (* whd in ⊢ (??%?); *)
           <(tape_move_null_action sig n (ctapes sig (states sig n M1) n outc1)) in ⊢ (???%); % 
          | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confL sig n (states ?? (single_finalTM ?? M2)) (states ?? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM2 … Hhalt) // ]
        ]
      |#_ @(ex_intro … (ctapes ??? outc1)) % 
        [@HMtrue @(\P Hacc) | >(mconfig_expand ??? outc2) @HM2 ]
      ]
    |>(mconfig_expand ??? outc2) whd in match (lift_confR ?????);
     * #H @False_ind @H @eq_f @eq_f >(mconfig_expand ??? outc2)
     @single_final // @(loop_Some ?????? Hloop2)
    ]
  |cases (HR3 (ctapes sig ?? outc1)) #k2 * #outc2 * #Hloop2 #HM3
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confR … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_mconfig ? (states sig n (ifTM sig n M1 (single_finalTM … M2) M3 acc)) n
          (inr (states sig n M1) ? (inr (states sig n (single_finalTM ?? M2)) ? (start sig n M3))) (ctapes ??? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig n (states ?? M1) (FinSum (states ?? (single_finalTM … M2)) (states ?? M3)))
          (step sig n M1) (step sig n (ifTM sig n M1 (single_finalTM ?? M2) M3 acc)) 
          (λc.halt sig n M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig n M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(mconfig_expand ??? outc1);
         whd in match (lift_confL ?????);
         >(trans_if_M1true_notacc … Hacc) 
          [@mconfig_eq // (* whd in ⊢ (??%?); *)
           <(tape_move_null_action sig n (ctapes sig (states sig n M1) n outc1)) in ⊢ (???%); % 
          | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confR sig n (states ?? (single_finalTM ?? M2)) (states ?? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM3 … Hhalt) // ]
        ]
      |>(mconfig_expand ??? outc2) whd in match (lift_confR ?????);
       #H destruct (H) 
      ]
    |#_ @(ex_intro … (ctapes ??? outc1)) % 
      [@HMfalse @(\Pf Hacc) | >(mconfig_expand ??? outc2) @HM3 ]
    ]
  ]
qed.
    
lemma acc_sem_if_app_guarded: ∀sig,n,M1,M2,M3,P,P2,Rtrue,Rfalse,R2,R3,R4,R5,acc.
  M1 ⊨ [acc: Rtrue, Rfalse] → 
  (GRealize ? n M2 P2 R2) → (∀t,t0.P t → Rtrue t t0 → P2 t0) → 
  M3 ⊨ R3 → 
  (∀t1,t2,t3. Rtrue t1 t3 → R2 t3 t2 → R4 t1 t2) → 
  (∀t1,t2,t3. Rfalse t1 t3 → R3 t3 t2 → R5 t1 t2) → 
  accGRealize ? n (ifTM sig n M1 (single_finalTM … M2) M3 acc) 
    (inr … (inl … (inr … start_nop))) P R4 R5 .
#sig #n #M1 #M2 #M3 #P #P2 #Rtrue #Rfalse #R2 #R3 #R4 #R5 #acc
#HRacc #HRtrue #Hinv #HRfalse #Hsub1 #Hsub2 
#t #HPt cases (acc_sem_if_guarded … HRacc HRtrue Hinv HRfalse t HPt)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.


