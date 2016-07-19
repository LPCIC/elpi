
include "turing/multi_to_mono/step.ma".

definition stop ≝ λsig,n.λM:mTM sig n.λc. 
   notb (halt sig n M (get_state (states sig n M) sig (S n) c (start sig n M))).
  
definition mtm_body ≝ λsig,n.λM:mTM sig n.
  ifTM ? (test_char … (stop sig n M))
    (single_finalTM ? (stepM (states sig n M) sig n (trans sig n M)))
    (nop … ) tc_true.

definition acc_mtm : ∀sig,n,M.states ? (mtm_body sig n M) ≝ 
  λsig,n,M. (inr … (inl … (inr … start_nop))).

definition mtm_R_true ≝ λsig,n.λM:mTM sig n.λt1,t2.
∀a:multi_sig (TA (HC (states sig n M) (S n)) sig) (S (S n)).
∀ls,rs. 
  t1 = midtape ? ls a rs → 
  let cin ≝ readback_config ? sig n (start … M) ls a rs in
  halt sig n M (cstate … cin) = false ∧ 
  R_stepM sig n M t1 t2.

definition mtm_R_false ≝ λsig,n.λM:mTM sig n.λt1,t2.
∀a:multi_sig (TA (HC (states sig n M) (S n)) sig) (S (S n)).
∀ls,rs. 
  t1 = midtape ? ls a rs → 
  let cin ≝ readback_config ? sig n (start … M) ls a rs in
  halt sig n M (cstate … cin) = true ∧ t1 = t2.

lemma sem_mtm_body: ∀sig,n,M.
  mtm_body sig n M ⊨ [acc_mtm sig n M: mtm_R_true sig n M, 
                                       mtm_R_false sig n M].
#sig #n #M
@(acc_sem_if_app ??????????? (sem_test_char … (stop sig n M))
   (sem_stepM sig n M)
   (sem_nop …))                             
[#tin #tout #t1 * * #c * #Hc #Hstop #Ht1 >Ht1 #Hstep
 #a #ls #rs #Htin % [2:@Hstep] >Htin in Hc; whd in ⊢ (??%?→?); 
 #H destruct (H) >state_readback @injective_notb @Hstop
|#tin #tout #t1 * #Hc #Ht1 #Htout #a #ls #rs #Htin % //
 >Htin in Hc; #Hc lapply (Hc … (refl ??)) #H @injective_notb @H
]
qed.
     
definition multi_to_monoTM ≝ λsig,n,M. 
  whileTM ? (mtm_body sig n M) (acc_mtm sig n M).

definition multi_to_mono_R ≝ λsig,n.λM:mTM sig n.λt1,t2.
∀a:multi_sig (TA (HC (states sig n M) (S n)) sig) (S (S n)).
∀ls,rs. 
  t1 = midtape ? ls a rs → 
  (∀i.regular_trace (TA (HC (states … M) (S n)) sig) (S(S n)) a ls rs i) → 
  is_head ?? (nth (S n) ? (vec … a) (blank ?)) = true →  
  no_head_in … ls →
  no_head_in … rs →
  let cin ≝ readback_config ? sig n (start … M) ls a rs in
  ∃a1:multi_sig (TA (HC (states sig n M) (S n)) sig) (S (S n)).
  ∃ls1,rs1,i. 
    t2 = midtape ? ls1 a1 rs1 ∧
    let cout ≝ readback_config ? sig n (start … M) ls1 a1 rs1 in  
    loopM sig n M i cin = Some ? cout.

theorem sem_universal: ∀sig,n,M.
  multi_to_monoTM sig n M ⊫ multi_to_mono_R sig n M.
#sig #n #M #intape #i #outc #Hloop
lapply (sem_while ?????? (sem_mtm_body sig n M) intape i outc Hloop) [%] -Hloop 
* #tin * #Hstar #Hfalse @(star_ind_l ??????? Hstar) -Hstar
[#a #ls #rs #Htin #_ #_ #_ #_ lapply (Hfalse … Htin) * #Hhalt #Houtc
%{a} %{ls} %{rs} %{1} % [<Houtc @Htin |@loop_S_true @Hhalt]
|#ta #tb #Hab #Hstar #Hind #a #ls #rs #Ha #H1 #H2 #H3 #H4 lapply (Hab … Ha)
 * #Hfalseb -Hab #Hab lapply (Hab … Ha H1 H2 H3 H4) -H1 -H2 -H3 -H4
 * #ls1 * #a1 * #rs1 * * #Htb #Hregb #Hrb_b
 lapply (Hind … Htb Hregb ???) [@daemon | @daemon |@daemon]
 * #a2 * #ls2 * #rs2 * #i * #Hc #Hloop
 %{a2} %{ls2} %{rs2} %{(S i)} % [@Hc] whd
 whd in match (loopM ?????); >Hfalseb whd in ⊢ (??%?); <Hrb_b @Hloop
]
qed. 
 

