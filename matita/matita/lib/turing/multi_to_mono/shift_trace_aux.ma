include "turing/basic_machines.ma".
include "turing/if_machine.ma".
include "turing/multi_to_mono/trace_alphabet.ma".

(* a machine that shift the i trace r starting from the bord of the trace *)

(* (λc.¬(nth i ? (vec … c) (blank ?))==blank ?)) *)
(* vec is a coercion. Why should I insert it? *)
definition mti_step ≝ λsig:FinSet.λn,i.
  ifTM (multi_sig sig n) (test_char ? (not_blank sig n i))
     (single_finalTM … 
       (ncombf_r (multi_sig sig n) (shift_i sig n i) (all_blanks sig n)))
     (nop ?) tc_true.
      
definition Rmti_step_true ≝ 
λsig,n,i,t1,t2. 
  ∃b:multi_sig sig n. (nth i ? (vec … b) (blank ?) ≠ blank ?) ∧
    ((∃ls,a,rs.
       t1 = midtape (multi_sig sig n) ls b (a::rs) ∧
       t2 = midtape (multi_sig sig n) ((shift_i sig n i b a)::ls) a rs) ∨
     (∃ls.
       t1 = midtape ? ls b [] ∧
       t2 = rightof ? (shift_i sig n i b (all_blanks sig n)) ls)).

(* 〈combf0,all_blank sig n〉 *)
definition Rmti_step_false ≝ 
  λsig,n,i,t1,t2.
    (∀ls,b,rs. t1 = midtape (multi_sig sig n) ls b rs →
     (nth i ? (vec … b) (blank ?) = blank ?)) ∧ t2 = t1.

lemma sem_mti_step :
  ∀sig,n,i.
  mti_step sig n i  ⊨ 
    [inr … (inl … (inr … start_nop)): Rmti_step_true sig n i, Rmti_step_false sig n i].
#sig #n #i
@(acc_sem_if_app (multi_sig sig n) … (sem_test_char …) 
  (sem_ncombf_r (multi_sig sig n) (shift_i sig n i)(all_blanks sig n)) 
  (sem_nop (multi_sig sig n)))
  [#intape #outtape #tapea whd in ⊢ (%→%→%); * * #c *
   #Hcur cases (current_to_midtape … Hcur) #ls * #rs #Hintape
   #ctest #Htapea * #Hout1 #Hout2 @(ex_intro … c) %
    [@(\Pf (injective_notb … )) @ctest]
   generalize in match Hintape; -Hintape cases rs
    [#Hintape %2 @(ex_intro …ls) % // @Hout1 >Htapea @Hintape
    |#a #rs1 #Hintape %1
     @(ex_intro … ls) @(ex_intro … a) @(ex_intro … rs1) % //
     @Hout2 >Htapea @Hintape
    ]
  |#intape #outtape #tapea whd in ⊢ (%→%→%);
   * #Htest #tapea #outtape 
   % // #ls #b #rs
   #intape lapply (Htest b ?) [>intape //] -Htest #Htest 
   lapply (injective_notb ? true Htest) -Htest #Htest @(\P Htest) 
  ]   
qed.
      
(* move tape i machine *)
definition mti ≝ 
  λsig,n,i.whileTM (multi_sig sig n) (mti_step sig n i) (inr … (inl … (inr … start_nop))). 

axiom daemon: ∀P:Prop.P.

definition R_mti ≝ λsig,n,i,t1,t2.
  (∀a,rs. t1 = rightof ? a rs → t2 = t1) ∧
  (∀a,ls,rs. 
    t1 = midtape (multi_sig sig n) ls a rs → 
    (nth i ? (vec … a) (blank ?) = blank ? ∧ t2 = t1) ∨
    ((∃rs1,b,rs2,rss.
      rs = rs1@b::rs2 ∧ 
      nth i ? (vec … b) (blank ?) = (blank ?) ∧
      (∀x. mem ? x (a::rs1) → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
      shift_l sig n i (a::rs1) rss ∧
      t2 = midtape (multi_sig sig n) ((reverse ? rss)@ls) b rs2) ∨
    (∃b,rss. 
      (∀x. mem ? x (a::rs) → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
      shift_l sig n i (a::rs) (rss@[b]) ∧
      t2 = rightof (multi_sig sig n) (shift_i sig n i b (all_blanks sig n)) 
       ((reverse ? rss)@ls)))).  

lemma sem_mti:
  ∀sig,n,i.
  WRealize (multi_sig sig n) (mti sig n i) (R_mti sig n i).
#sig #n #i #inc #j #outc #Hloop
lapply (sem_while … (sem_mti_step sig n i) inc j outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ whd in ⊢ (% → ?); * #H1 #H2 % 
  [#a #rs #Htape1 @H2
  |#a #ls #rs #Htapea % % [@(H1 … Htapea) |@H2]
  ]
| #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH -HRfalse whd in ⊢ (%→%); 
  * #IH1 #IH2 %
  [#b0 #ls #Htapeb cases Hstar1 #b * #_ *
    [* #ls0 * #a * #rs0 * >Htapeb #H destruct (H)
    |* #ls0 * >Htapeb #H destruct (H)
    ]
  |#b0 #ls #rs #Htapeb cases Hstar1 #b * #btest *
  [* #ls1 * #a * #rs1 * >Htapeb #H destruct (H) #Htapec 
   %2 cases (IH2 … Htapec)
    [(* case a = None *)
     * #testa #Hout %1
     %{[ ]} %{a} %{rs1} %{[shift_i sig n i b a]} %
      [%[%[% // |#x #Hb >(mem_single ??? Hb) // ] 
        |@daemon]
      |>Hout >reverse_single @Htapec
      ] 
    |*
      [ (* case a \= None and exists b = None *) -IH1 -IH2 #IH
        %1 cases IH -IH #rs10 * #b0 * #rs2 * #rss * * * *
        #H1 #H2 #H3 #H4 #H5
        %{(a::rs10)} %{b0} %{rs2} %{(shift_i sig n i b a::rss)}
        %[%[%[%[>H1 //|@H2]
            |#x * [#eqxa >eqxa (*?? *) @daemon|@H3]]
          |@daemon]
        |>H5 >reverse_cons >associative_append //
        ]
      | (* case a \= None and we reach the end of the (full) tape *) -IH1 -IH2 #IH
        %2 cases IH -IH #b0 * #rss * * #H1 #H2 #H3
        %{b0} %{(shift_i sig n i b a::rss)} 
        %[%[#x * [#eqxb >eqxb @btest|@H1]
           |@daemon]
        |>H3 >reverse_cons >associative_append //
        ]
      ]
    ]
  |(* b \= None but the left tape is empty *)
   * #ls0 * >Htapeb #H destruct (H) #Htapec
   %2 %2 %{b} %{[ ]} 
   %[%[#x * [#eqxb >eqxb @btest|@False_ind]
      |@daemon (*shift of  dingle char OK *)]
    |>(IH1 … Htapec) >Htapec //
    ]
  ]
qed.
    
lemma WF_mti_niltape:
  ∀sig,n,i. WF ? (inv ? (Rmti_step_true sig n i)) (niltape ?).
#sig #n #i @wf #t1 whd in ⊢ (%→?); * #b * #_ *
  [* #ls * #a * #rs * #H destruct|* #ls * #H destruct ]
qed.

lemma WF_mti_rightof:
  ∀sig,n,i,a,ls. WF ? (inv ? (Rmti_step_true sig n i)) (rightof ? a ls).
#sig #n #i #a #ls @wf #t1 whd in ⊢ (%→?); * #b * #_ *
  [* #ls * #a * #rs * #H destruct|* #ls * #H destruct ]
qed.

lemma WF_mti_leftof:
  ∀sig,n,i,a,ls. WF ? (inv ? (Rmti_step_true sig n i)) (leftof ? a ls).
#sig #n #i #a #ls @wf #t1 whd in ⊢ (%→?); * #b * #_ *
  [* #ls * #a * #rs * #H destruct|* #ls * #H destruct ]
qed.

lemma terminate_mti:
  ∀sig,n,i.∀t. Terminate ? (mti sig n i) t.
#sig #n #i #t @(terminate_while … (sem_mti_step sig n i)) [%]
cases t // #ls #c #rs lapply c -c lapply ls -ls  elim rs 
  [#ls #c @wf #t1 whd in ⊢ (%→?); * #b * #_ *
    [* #ls1 * #a * #rs1 * #H destruct
    |* #ls1 * #H destruct #Ht1 >Ht1 //
    ]
  |#a #rs1 #Hind #ls #c @wf #t1 whd in ⊢ (%→?); * #b * #_ *
    [* #ls1 * #a2 * #rs2 * #H destruct (H) #Ht1 >Ht1 //
    |* #ls1 *  #H destruct
    ]
  ]
qed.

lemma ssem_mti: ∀sig,n,i.
  Realize ? (mti sig n i) (R_mti sig n i).
/2/ qed.
   
