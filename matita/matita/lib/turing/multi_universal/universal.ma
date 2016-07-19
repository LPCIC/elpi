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

include "turing/auxiliary_multi_machines.ma".
include "turing/multi_universal/unistep.ma".

definition stop ≝ λc.
  match c with [ bit b ⇒ notb b | _ ⇒ true].
  
definition uni_body ≝ 
  ifTM ?? (mtestR ? cfg 2 stop)
    (single_finalTM ?? unistep)
    (nop …) (mtestR_acc ? cfg 2 stop).

definition acc_body : states ?? uni_body ≝ (inr … (inl … (inr … start_nop))).

definition ub_R_true ≝ λM,t1,t2.
  ∀c: nconfig (no_states M). 
  t1=low_tapes M c→
    t2=low_tapes M (step FinBool M c) ∧ halt ? M (cstate … c) = false.
  
definition ub_R_false ≝ λM,t1,t2.
  ∀c: nconfig (no_states M).  
  t1 = low_tapes M c → t1 = t2 ∧ halt ? M (cstate … c) = true.

lemma sem_uni_body: ∀M.
  uni_body ⊨ [acc_body: ub_R_true M, ub_R_false M].
#M #cf 
@(acc_sem_if_app ????????????
   (sem_mtestR ? cfg 2 stop (le_S ?? (le_n 1)))
   (sem_unistep M)
   (sem_nop …))
[#t1 #t2 #t3 whd in ⊢ (%→?); #Htest #Ht2 * #q #Mt #Ht1
 >Ht1 in Htest; >cfg_low_tapes whd in match (bits_of_state ???);
 #Htest lapply (Htest … (refl ??)) * <Ht1 #Ht3 #Hstop >Ht3 in Ht2;
 #Ht2 % [@Ht2 //] lapply Hstop  whd in match (nhalt ??); 
 cases (nhalt M q) whd in match (stop ?); * /2/
|#t1 #t2 #t3 whd in ⊢ (%→?); #Htest #Hnop >Hnop -Hnop * #q #Mt #Ht1 >Ht1 in Htest;
 >cfg_low_tapes whd in match (bits_of_state ???); 
 #Htest lapply (Htest … (refl ??)) whd in match (nhalt ??); 
 cases (nhalt M q) whd in match (stop ?); * /2/ 
]
qed.

definition universalTM ≝ whileTM ?? uni_body acc_body.

definition low_R ≝ λM,q,R.λt1,t2:Vector (tape FSUnialpha) 3.
    ∀Mt. t1 = low_tapes M (mk_config ?? q Mt) → 
    ∃cout. R Mt (ctape … cout) ∧
    halt ? M (cstate … cout) = true ∧ t2 = low_tapes M cout.

theorem sem_universal: ∀M:normalTM. ∀q.
  universalTM ⊫ low_R M q (R_TM FinBool M q).
#M #q #intape #i #outc #Hloop
lapply (sem_while … (sem_uni_body M … ) intape i outc Hloop) [%] -Hloop 
* #ta * #Hstar lapply q -q @(star_ind_l ??????? Hstar) -Hstar
  [#q whd in ⊢ (%→?); #HFalse whd #Mt #Hta 
   lapply (HFalse … Hta) * #Hta1 #Hhalt %{(mk_config ?? q Mt)} %
    [%[%{1} %{(mk_config ?? q Mt)} % // whd in ⊢ (??%?); >Hhalt % |@Hhalt]
    |<Hta1 @Hta  
    ]
  |#t1 #t2 whd in ⊢ (%→?); #Hstep #Hstar #IH #q #Hta whd #Mt #Ht1
   lapply (Hstep … Ht1) * -Hstep #Ht2 #Hhalt
   lapply(IH (cstate … (step FinBool M (mk_config ?? q Mt))) Hta ??) [@Ht2|skip] -IH 
   * #cout * * #HRTM #Hhalt1 #Houtc
   %{cout} 
   %[%[cases HRTM #k * #outc1 * <config_expand #Hloop #Houtc1
       %{(S k)} %{outc1} % 
        [whd in ⊢ (??%?); >Hhalt whd in ⊢ (??%?); @Hloop 
        |@Houtc1
        ]
      |@Hhalt1]
    |@Houtc
    ]
  ] 
qed.
  
theorem sem_universal2: ∀M:normalTM. ∀R.
  M ⊫ R → universalTM ⊫ (low_R M (start ? M) R).
#M #R #HMR lapply (sem_universal … M (start ? M)) @WRealize_to_WRealize
#t1 #t2 whd in ⊢ (%→%); #H #tape1 #Htape1 cases (H ? Htape1)
#c * * #HRTM #Hhalt #Ht2 %{c}
% [% [@(R_TM_to_R … HRTM) @HMR | //] | //]
qed.
 
(* termination *)


lemma halting_case: ∀M:normalTM.∀t,q. halt ? M q = true → 
  universalTM↓low_tapes M (mk_config ?? q t). 
#M #t #q #Hhalt
@(terminate_while ?? uni_body ????? (sem_uni_body … M)) [%]
% #ta whd in ⊢ (%→?); #H cases (H … (refl ??)) #_ >Hhalt 
#Habs destruct (Habs)
qed.

theorem terminate_UTM: ∀M:normalTM.∀t. 
  M ↓ t → universalTM ↓ (low_tapes M (mk_config ?? (start ? M) t)).
#M #t #H @(terminate_while ?? uni_body ????? (sem_uni_body … M)) [%]
lapply H -H * #x (* we need to generalize to an arbitrary initial configuration *)
whd in match (initc ? M t); generalize in match (start ? M); lapply t -t
elim x
  [#t #q * #outc whd in ⊢ (??%?→?); #Habs destruct
  |#n #Hind #t #q cases (true_or_false (halt ? M q)) #Hhaltq
    [* #outc whd in ⊢ (??%?→?); >Hhaltq whd in ⊢ (??%?→?); #HSome destruct (HSome)
     % #ta whd in ⊢ (%→?); #H cases (H … (refl ??)) #_ >Hhaltq 
     #Habs destruct (Habs) 
  |* #outc whd in ⊢ (??%?→?); >Hhaltq whd in ⊢ (??%?→?); #Hloop 
   % #t1 whd in ⊢ (%→?); #Hstep lapply (Hstep … (refl ??)) *
   #Ht1 #_ >Ht1 @Hind %{outc} <config_expand @Hloop
  ]
qed.

