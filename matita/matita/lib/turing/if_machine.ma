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

include "turing/mono.ma".

(**************************** single final machine ****************************)

definition single_finalTM ≝ 
  λsig.λM:TM sig.seq ? M (nop ?).

lemma sem_single_final: ∀sig.∀M: TM sig.∀R.
  M ⊨ R → single_finalTM sig M ⊨ R.
#sig #M #R #HR #intape 
cases (sem_seq ????? HR (sem_nop …) intape)
#k * #outc * #Hloop * #ta * #Hta whd in ⊢ (%→?); #Houtc
@(ex_intro ?? k) @(ex_intro ?? outc) %  [ @Hloop | >Houtc // ]
qed.

lemma single_final: ∀sig.∀M: TM sig.∀q1,q2.
  halt ? (single_finalTM sig M) q1 = true 
    →  halt ? (single_finalTM sig M) q2 = true → q1=q2.
#sig #M * 
  [#q1M #q2 whd in match (halt ???); #H destruct
  |#q1nop *
    [#q2M #_ whd in match (halt ???); #H destruct
    |#q2nop #_ #_ @eq_f normalize @nop_single_state
    ]
  ]
qed.
  
(******************************** if machine **********************************)

definition if_trans ≝ λsig. λM1,M2,M3 : TM sig. λq:states sig M1.
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig M1 s1 then
        if s1==q then 〈inr … (inl … (start sig M2)), None ?,N〉
        else 〈inr … (inr … (start sig M3)), None ?,N〉
      else let 〈news1,newa,m〉 ≝ trans sig M1 〈s1,a〉 in
       〈inl … news1,newa,m〉
  | inr s' ⇒ 
      match s' with
      [ inl s2 ⇒ let 〈news2,newa,m〉 ≝ trans sig M2 〈s2,a〉 in
         〈inr … (inl … news2),newa,m〉
      | inr s3 ⇒ let 〈news3,newa,m〉 ≝ trans sig M3 〈s3,a〉 in
         〈inr … (inr … news3),newa,m〉
      ]
  ]. 
 
definition ifTM ≝ λsig. λcondM,thenM,elseM : TM sig.
  λqacc: states sig condM.
  mk_TM sig 
    (FinSum (states sig condM) (FinSum (states sig thenM) (states sig elseM)))
    (if_trans sig condM thenM elseM qacc)
    (inl … (start sig condM))
    (λs.match s with
      [ inl _ ⇒ false 
      | inr s' ⇒ match s' with 
        [ inl s2 ⇒ halt sig thenM s2
        | inr s3 ⇒ halt sig elseM s3 ]]).

(****************************** lifting lemmas ********************************)
lemma trans_if_liftM1 : ∀sig,M1,M2,M3,acc,s,a,news,newa,move.
  halt ? M1 s = false → 
  trans sig M1 〈s,a〉 = 〈news,newa,move〉 → 
  trans sig (ifTM sig M1 M2 M3 acc) 〈inl … s,a〉 = 〈inl … news,newa,move〉.
#sig * #Q1 #T1 #init1 #halt1 #M2 #M3 #acc #s #a #news #newa #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_if_liftM2 : ∀sig,M1,M2,M3,acc,s,a,news,newa,move.
  halt ? M2 s = false → 
  trans sig M2 〈s,a〉 = 〈news,newa,move〉 → 
  trans sig (ifTM sig M1 M2 M3 acc) 〈inr … (inl … s),a〉 = 〈inr… (inl … news),newa,move〉.
#sig #M1 * #Q2 #T2 #init2 #halt2 #M3 #acc #s #a #news #newa #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_if_liftM3 : ∀sig,M1,M2,M3,acc,s,a,news,newa,move.
  halt ? M3 s = false → 
  trans sig M3 〈s,a〉 = 〈news,newa,move〉 → 
  trans sig (ifTM sig M1 M2 M3 acc) 〈inr … (inr … s),a〉 = 〈inr… (inr … news),newa,move〉.
#sig #M1 * #Q2 #T2 #init2 #halt2 #M3 #acc #s #a #news #newa #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma step_if_liftM1 : ∀sig,M1,M2,M3,acc,c0.
 halt ? M1 (cstate ?? c0) = false → 
 step sig (ifTM sig M1 M2 M3 acc) (lift_confL sig (states ? M1) ? c0) =
 lift_confL sig (states ? M1) ? (step sig M1 c0).
#sig #M1 #M2 #M3 #acc * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  * #s0 #a0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ]
  whd in ⊢ (???(????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_if_liftM1 … Hhalt Heq) //
qed.

lemma step_if_liftM2 : ∀sig,M1,M2,M3,acc,c0.
 halt ? M2 (cstate ?? c0) = false → 
 step sig (ifTM sig M1 M2 M3 acc) (lift_confR sig ?? (lift_confL sig ?? c0)) =
 lift_confR sig ?? (lift_confL sig ?? (step sig M2 c0)).
#sig #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 #M3 #acc * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  * #s0 #a0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ] 
  whd in match (step ? M2 ?); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_if_liftM2 … Hhalt Heq) //
qed.

lemma step_if_liftM3 : ∀sig,M1,M2,M3,acc,c0.
 halt ? M3 (cstate ?? c0) = false → 
 step sig (ifTM sig M1 M2 M3 acc) (lift_confR sig ?? (lift_confR sig ?? c0)) =
 lift_confR sig ?? (lift_confR sig ?? (step sig M3 c0)).
#sig #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 #M3 #acc * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  * #s0 #a0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ] 
  whd in match (step ? M3 ?); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_if_liftM3 … Hhalt Heq) //
qed.

lemma trans_if_M1true_acc : ∀sig,M1,M2,M3,acc,s,a.
  halt ? M1 s = true → s==acc = true →
  trans sig (ifTM sig M1 M2 M3 acc) 〈inl … s,a〉 = 〈inr … (inl … (start ? M2)),None ?,N〉.
#sig #M1 #M2 #M3 #acc #s #a #Hhalt #Hacc whd in ⊢ (??%?); >Hhalt >Hacc %
qed.

lemma trans_if_M1true_notacc : ∀sig,M1,M2,M3,acc,s,a.
  halt ? M1 s = true → s==acc = false →
  trans sig (ifTM sig M1 M2 M3 acc) 〈inl … s,a〉 = 〈inr … (inr … (start ? M3)),None ?,N〉.
#sig #M1 #M2 #M3 #acc #s #a #Hhalt #Hacc whd in ⊢ (??%?); >Hhalt >Hacc %
qed.

(******************************** semantics ***********************************)
lemma sem_if: ∀sig.∀M1,M2,M3:TM sig.∀Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ [acc: Rtrue,Rfalse] → M2 ⊨ R2 → M3 ⊨ R3 → 
    ifTM sig M1 M2 M3 acc ⊨ (Rtrue ∘ R2) ∪ (Rfalse ∘ R3).
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HR3 #t 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ?? outc1 == acc)) #Hacc
  [cases (HR2 (ctape sig ? outc1)) #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confL … outc2))) %
    [@(loop_merge ?????????
     (mk_config ? (FinSum (states sig M1) (FinSum (states sig M2) (states sig M3)))
      (inr (states sig M1) ? (inl (states sig M2) (states sig M3) (start sig M2))) (ctape ?? outc1) )
     ? 
     (loop_lift ??? 
       (lift_confL sig (states ? M1) (FinSum (states ? M2) (states ? M3)))
       (step sig M1) (step sig (ifTM sig M1 M2 M3 acc)) 
       (λc.halt sig M1 (cstate … c)) 
       (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
       … Hloop1))
      [* *
        [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
        | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
      |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
      |#x <p_halt_liftL %
      |whd in ⊢ (??%?); >(config_expand ?? outc1);
       whd in match (lift_confL ????);
       >(trans_if_M1true_acc … Hacc) 
        [% | @(loop_Some ?????? Hloop1)]
      |cases outc1 #s1 #t1 %
      |@(loop_lift ??? 
         (λc.(lift_confR … (lift_confL sig (states ? M2) (states ? M3) c)))
         … Hloop2) 
        [ * #s2 #t2 %
        | #c0 #Hhalt >(step_if_liftM2 … Hhalt) // ]
      ]
    |%1 @(ex_intro … (ctape ?? outc1)) % 
      [@HMtrue @(\P Hacc) | >(config_expand ?? outc2) @HM2 ]
    ]
  |cases (HR3 (ctape sig ? outc1)) #k2 * #outc2 * #Hloop2 #HM3
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confR … outc2))) %
    [@(loop_merge ?????????
     (mk_config ? (FinSum (states sig M1) (FinSum (states sig M2) (states sig M3)))
      (inr (states sig M1) ? (inr (states sig M2) (states sig M3) (start sig M3))) (ctape ?? outc1) )
     ? 
     (loop_lift ??? 
       (lift_confL sig (states ? M1) (FinSum (states ? M2) (states ? M3)))
       (step sig M1) (step sig (ifTM sig M1 M2 M3 acc)) 
       (λc.halt sig M1 (cstate … c)) 
       (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
       … Hloop1))
      [* *
        [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
        | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
      |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
      |#x <p_halt_liftL %
      |whd in ⊢ (??%?); >(config_expand ?? outc1);
       whd in match (lift_confL ????);
       >(trans_if_M1true_notacc … Hacc) 
        [% | @(loop_Some ?????? Hloop1)]
      |cases outc1 #s1 #t1 %
      |@(loop_lift ??? 
         (λc.(lift_confR … (lift_confR sig (states ? M2) (states ? M3) c)))
         … Hloop2) 
        [ * #s2 #t2 %
        | #c0 #Hhalt >(step_if_liftM3 … Hhalt) // ]
      ]
    |%2 @(ex_intro … (ctape ?? outc1)) % 
      [@HMfalse @(\Pf Hacc) | >(config_expand ?? outc2) @HM3 ]
    ]
  ]
qed.

lemma sem_if_app: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,acc.
  accRealize sig M1 acc Rtrue Rfalse  → M2 ⊨ R2  → M3 ⊨ R3 →  
    (∀t1,t2,t3. (Rtrue t1 t3 ∧ R2 t3 t2) ∨ (Rfalse t1 t3 ∧ R3 t3 t2) → R4 t1 t2) → 
    ifTM sig M1 M2 M3 acc ⊨ R4.
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #acc
#HRacc #HRtrue #HRfalse #Hsub
#t cases (sem_if … HRacc HRtrue HRfalse t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop] cases Houtc
  [* #t3 * #Hleft #Hright @(Hsub … t3) %1 /2/
  |* #t3 * #Hleft #Hright @(Hsub … t3) %2 /2/ ]
qed.

(* weak 
lemma sem_if_app: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,acc.
  accRealize sig M1 acc Rtrue Rfalse  → M2 ⊨ R2  → M3 ⊨ R3 →  
    (∀t1,t2,t3. (Rtrue t1 t3 → R2 t3 t2) ∨ (Rfalse t1 t3 → R3 t3 t2) → R4 t1 t2) → 
    ifTM sig M1 M2 M3 acc ⊨ R4.
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #acc
#HRacc #HRtrue #HRfalse #Hsub
#t cases (sem_if … HRacc HRtrue HRfalse t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop] cases Houtc
  [* #t3 * #Hleft #Hright @(Hsub … t3) %1 /2/
  |* #t3 * #Hleft #Hright @(Hsub … t3) %2 /2/ ]
qed.
*)

(* we can probably use acc_sem_if to prove sem_if *)
(* for sure we can use acc_sem_if_guarded to prove acc_sem_if *)
lemma acc_sem_if: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ [acc: Rtrue, Rfalse]  → M2 ⊨ R2 → M3 ⊨ R3 → 
  ifTM sig M1 (single_finalTM … M2) M3 acc ⊨
     [inr … (inl … (inr … start_nop)): Rtrue ∘ R2, Rfalse ∘ R3].
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HR3 #t 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ?? outc1 == acc)) #Hacc
  [lapply (sem_single_final … HR2) -HR2 #HR2
   cases (HR2 (ctape sig ? outc1)) #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) 
   @(ex_intro … (lift_confR … (lift_confL … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_config ? (states sig (ifTM sig M1 (single_finalTM … M2) M3 acc))
          (inr (states sig M1) ? (inl ? (states sig M3) (start sig (single_finalTM sig M2)))) (ctape ?? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig (states ? M1) (FinSum (states ? (single_finalTM … M2)) (states ? M3)))
          (step sig M1) (step sig (ifTM sig M1 (single_finalTM ? M2) M3 acc)) 
          (λc.halt sig M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(config_expand ?? outc1);
         whd in match (lift_confL ????);
         >(trans_if_M1true_acc … Hacc) 
          [% | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confL sig (states ? (single_finalTM ? M2)) (states ? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM2 … Hhalt) // ]
        ]
      |#_ @(ex_intro … (ctape ?? outc1)) % 
        [@HMtrue @(\P Hacc) | >(config_expand ?? outc2) @HM2 ]
      ]
    |>(config_expand ?? outc2) whd in match (lift_confR ????);
     * #H @False_ind @H @eq_f @eq_f >(config_expand ?? outc2)
     @single_final // @(loop_Some ?????? Hloop2)
    ]
  |cases (HR3 (ctape sig ? outc1)) #k2 * #outc2 * #Hloop2 #HM3
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confR … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_config ? (states sig (ifTM sig M1 (single_finalTM … M2) M3 acc))
          (inr (states sig M1) ? (inr (states sig (single_finalTM ? M2)) ? (start sig M3))) (ctape ?? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig (states ? M1) (FinSum (states ? (single_finalTM … M2)) (states ? M3)))
          (step sig M1) (step sig (ifTM sig M1 (single_finalTM ? M2) M3 acc)) 
          (λc.halt sig M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(config_expand ?? outc1);
         whd in match (lift_confL ????);
         >(trans_if_M1true_notacc … Hacc) 
          [% | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confR sig (states ? (single_finalTM ? M2)) (states ? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM3 … Hhalt) // ]
        ]
      |>(config_expand ?? outc2) whd in match (lift_confR ????);
       #H destruct (H) 
      ]
    |#_ @(ex_intro … (ctape ?? outc1)) % 
      [@HMfalse @(\Pf Hacc) | >(config_expand ?? outc2) @HM3 ]
    ]
  ]
qed.
    
lemma acc_sem_if_app: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,R5,acc.
  M1 ⊨ [acc: Rtrue, Rfalse] → M2 ⊨ R2 → M3 ⊨ R3 → 
    (∀t1,t2,t3. Rtrue t1 t3 → R2 t3 t2 → R4 t1 t2) → 
    (∀t1,t2,t3. Rfalse t1 t3 → R3 t3 t2 → R5 t1 t2) → 
     ifTM sig M1 (single_finalTM … M2) M3 acc ⊨ 
       [inr … (inl … (inr … start_nop)): R4, R5].    
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #R5 #acc
#HRacc #HRtrue #HRfalse #Hsub1 #Hsub2 
#t cases (acc_sem_if … HRacc HRtrue HRfalse t)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.

lemma sem_single_final_guarded: ∀sig.∀M: TM sig.∀Pre,R.
  GRealize sig M Pre R → GRealize sig (single_finalTM sig M) Pre R.
#sig #M #Pre #R #HR #intape #HPre 
cases (sem_seq_guarded ??????? HR (Realize_to_GRealize ?? (λt.True) ? (sem_nop …)) ?? HPre) //
#k * #outc * #Hloop * #ta * #Hta whd in ⊢ (%→?); #Houtc
@(ex_intro ?? k) @(ex_intro ?? outc) %  [ @Hloop | >Houtc // ]
qed.
    
lemma acc_sem_if_guarded: ∀sig,M1,M2,M3,P,P2,Rtrue,Rfalse,R2,R3,acc.
  M1 ⊨ [acc: Rtrue, Rfalse]  → 
  (GRealize ? M2 P2 R2) → (∀t,t0.P t → Rtrue t t0 → P2 t0) → 
  M3 ⊨ R3 → 
  accGRealize ? (ifTM sig M1 (single_finalTM … M2) M3 acc) 
    (inr … (inl … (inr … start_nop))) P (Rtrue ∘ R2) (Rfalse ∘ R3).
#sig #M1 #M2 #M3 #P #P2 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HP2 #HR3 #t #HPt 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ?? outc1 == acc)) #Hacc
  [lapply (sem_single_final_guarded … HR2) -HR2 #HR2
   cases (HR2 (ctape sig ? outc1) ?)
   [|@HP2 [||@HMtrue @(\P Hacc)] // ]
   #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) 
   @(ex_intro … (lift_confR … (lift_confL … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_config ? (states sig (ifTM sig M1 (single_finalTM … M2) M3 acc))
          (inr (states sig M1) ? (inl ? (states sig M3) (start sig (single_finalTM sig M2)))) (ctape ?? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig (states ? M1) (FinSum (states ? (single_finalTM … M2)) (states ? M3)))
          (step sig M1) (step sig (ifTM sig M1 (single_finalTM ? M2) M3 acc)) 
          (λc.halt sig M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(config_expand ?? outc1);
         whd in match (lift_confL ????);
         >(trans_if_M1true_acc … Hacc) 
          [% | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confL sig (states ? (single_finalTM ? M2)) (states ? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM2 … Hhalt) // ]
        ]
      |#_ @(ex_intro … (ctape ?? outc1)) % 
        [@HMtrue @(\P Hacc) | >(config_expand ?? outc2) @HM2 ]
      ]
    |>(config_expand ?? outc2) whd in match (lift_confR ????);
     * #H @False_ind @H @eq_f @eq_f >(config_expand ?? outc2)
     @single_final // @(loop_Some ?????? Hloop2)
    ]
  |cases (HR3 (ctape sig ? outc1)) #k2 * #outc2 * #Hloop2 #HM3
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confR … outc2))) %
    [%
      [@(loop_merge ?????????
         (mk_config ? (states sig (ifTM sig M1 (single_finalTM … M2) M3 acc))
          (inr (states sig M1) ? (inr (states sig (single_finalTM ? M2)) ? (start sig M3))) (ctape ?? outc1) )
         ? 
         (loop_lift ??? 
          (lift_confL sig (states ? M1) (FinSum (states ? (single_finalTM … M2)) (states ? M3)))
          (step sig M1) (step sig (ifTM sig M1 (single_finalTM ? M2) M3 acc)) 
          (λc.halt sig M1 (cstate … c)) 
          (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
          … Hloop1))
        [* *
          [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
          | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
        |#c0 #Hhalt >(step_if_liftM1 … Hhalt) // 
        |#x <p_halt_liftL %
        |whd in ⊢ (??%?); >(config_expand ?? outc1);
         whd in match (lift_confL ????);
         >(trans_if_M1true_notacc … Hacc) 
          [% | @(loop_Some ?????? Hloop1)]
        |cases outc1 #s1 #t1 %
        |@(loop_lift ??? 
           (λc.(lift_confR … (lift_confR sig (states ? (single_finalTM ? M2)) (states ? M3) c)))
           … Hloop2) 
          [ * #s2 #t2 %
          | #c0 #Hhalt >(step_if_liftM3 … Hhalt) // ]
        ]
      |>(config_expand ?? outc2) whd in match (lift_confR ????);
       #H destruct (H) 
      ]
    |#_ @(ex_intro … (ctape ?? outc1)) % 
      [@HMfalse @(\Pf Hacc) | >(config_expand ?? outc2) @HM3 ]
    ]
  ]
qed.
    
lemma acc_sem_if_app_guarded: ∀sig,M1,M2,M3,P,P2,Rtrue,Rfalse,R2,R3,R4,R5,acc.
  M1 ⊨ [acc: Rtrue, Rfalse] → 
  (GRealize ? M2 P2 R2) → (∀t,t0.P t → Rtrue t t0 → P2 t0) → 
  M3 ⊨ R3 → 
  (∀t1,t2,t3. Rtrue t1 t3 → R2 t3 t2 → R4 t1 t2) → 
  (∀t1,t2,t3. Rfalse t1 t3 → R3 t3 t2 → R5 t1 t2) → 
  accGRealize ? (ifTM sig M1 (single_finalTM … M2) M3 acc) 
    (inr … (inl … (inr … start_nop))) P R4 R5 .
#sig #M1 #M2 #M3 #P #P2 #Rtrue #Rfalse #R2 #R3 #R4 #R5 #acc
#HRacc #HRtrue #Hinv #HRfalse #Hsub1 #Hsub2 
#t #HPt cases (acc_sem_if_guarded … HRacc HRtrue Hinv HRfalse t HPt)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.


