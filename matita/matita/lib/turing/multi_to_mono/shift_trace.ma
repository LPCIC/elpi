include "turing/auxiliary_machines1.ma".
include "turing/multi_to_mono/shift_trace_aux.ma".

(******************************************************************************)
(* mtiL: complete move L for tape i. We reaching the left border of trace i,  *)
(* add a blank if there is no more tape, then move the i-trace and finally    *)
(* come back to the head position.                                            *)
(******************************************************************************)

(* we say that a tape is regular if for any trace after the first blank we
  only have other blanks *)
  
definition all_blanks_in ≝ λsig,l.
  ∀x. mem ? x l → x = blank sig.  
 
definition regular_i  ≝ λsig,n.λl:list (multi_sig sig n).λi.
  all_blanks_in ? (after_blank ? (trace sig n i l)).

definition regular_trace ≝ λsig,n,a.λls,rs:list (multi_sig sig n).λi.
  Or (And (regular_i sig n (a::ls) i) (regular_i sig n rs i))
     (And (regular_i sig n ls i) (regular_i sig n (a::rs) i)).
         
axiom regular_tail: ∀sig,n,l,i.
  regular_i sig n l i → regular_i sig n (tail ? l) i.
  
axiom regular_extend: ∀sig,n,l,i.
   regular_i sig n l i → regular_i sig n (l@[all_blanks sig n]) i.

axiom all_blank_after_blank: ∀sig,n,l1,b,l2,i. 
  nth i ? (vec … b) (blank ?) = blank ? → 
  regular_i sig n (l1@b::l2) i → all_blanks_in ? (trace sig n i l2).
   
lemma regular_trace_extl:  ∀sig,n,a,ls,rs,i.
  regular_trace sig n a ls rs i → 
    regular_trace sig n a (ls@[all_blanks sig n]) rs i.
#sig #n #a #ls #rs #i *
  [* #H1 #H2 % % // @(regular_extend … H1)
  |* #H1 #H2 %2 % // @(regular_extend … H1)
  ]
qed.

lemma regular_cons_hd_rs: ∀sig,n.∀a:multi_sig sig n.∀ls,rs1,rs2,i.
  regular_trace sig n a ls (rs1@rs2) i → 
    regular_trace sig n a ls (rs1@((hd ? rs2 (all_blanks …))::(tail ? rs2))) i.
#sig #n #a #ls #rs1 #rs2 #i cases rs2 [2: #b #tl #H @H] 
*[* #H1 >append_nil #H2 %1 % 
   [@H1 | whd in match (hd ???); @(regular_extend … rs1) //]
 |* #H1 >append_nil #H2 %2 % 
   [@H1 | whd in match (hd ???); @(regular_extend … (a::rs1)) //]
 ]
qed.

lemma eq_trace_to_regular : ∀sig,n.∀a1,a2:multi_sig sig n.∀ls1,ls2,rs1,rs2,i.
   nth i ? (vec … a1) (blank ?) = nth i ? (vec … a2) (blank ?) →
   trace sig n i ls1 = trace sig n i ls2 → 
   trace sig n i rs1 = trace sig n i rs2 →
   regular_trace sig n a1 ls1 rs1 i → 
     regular_trace sig n a2 ls2 rs2 i.
#sig #n #a1 #a2 #ls1 #ls2 #rs1 #rs2 #i #H1 #H2 #H3 #H4
whd in match (regular_trace ??????); whd in match (regular_i ????);
whd in match (regular_i ?? rs2 ?); whd in match (regular_i ?? ls2 ?);
whd in match (regular_i ?? (a2::rs2) ?); whd in match (trace ????);
<trace_def whd in match (trace ??? (a2::rs2)); <trace_def 
<H1 <H2 <H3 @H4
qed.

(******************************* move_to_blank_L ******************************)
(* we compose machines together to reduce the number of output cases, and 
   improve semantics *)
   
definition move_to_blank_L ≝ λsig,n,i.
  (move_until ? L (not_blank sig n i)) · extend ? (all_blanks sig n).

(*
definition R_move_to_blank_L ≝ λsig,n,i,t1,t2.
(current ? t1 = None ? → 
  t2 = midtape (multi_sig sig n) (left ? t1) (all_blank …) (right ? t1)) ∧
∀ls,a,rs.t1 = midtape ? ls a rs → 
  ((no_blank sig n i a = false) ∧ t2 = t1) ∨
  (∃b,ls1,ls2.
    (no_blank sig n i b = false) ∧ 
    (∀j.j ≤n → to_blank_i ?? j (ls1@b::ls2) = to_blank_i ?? j ls) ∧
    t2 = midtape ? ls2 b ((reverse ? (a::ls1))@rs)). 
*)

definition R_move_to_blank_L ≝ λsig,n,i,t1,t2.
(current ? t1 = None ? → 
  t2 = midtape (multi_sig sig n) (left ? t1) (all_blanks …) (right ? t1)) ∧
∀ls,a,rs.
  t1 = midtape (multi_sig sig n) ls a rs → 
  regular_i sig n (a::ls) i →
  (∀j. j ≠ i → regular_trace … a ls rs j) →
  (∃b,ls1,ls2.
    (regular_i sig n (ls1@b::ls2) i) ∧ 
    (∀j. j ≠ i → regular_trace … 
      (hd ? (ls1@b::ls2) (all_blanks …)) (tail ? (ls1@b::ls2)) rs j) ∧ 
    (not_blank sig n i b = false) ∧ 
    (hd (multi_sig sig n) (ls1@[b]) (all_blanks …) = a) ∧ (* not implied by the next fact *)
    (∀j.j < n → to_blank_i ?? j (ls1@b::ls2) = to_blank_i ?? j (a::ls)) ∧
    t2 = midtape ? ls2 b ((reverse ? ls1)@rs)).

theorem sem_move_to_blank_L: ∀sig,n,i. 
  move_to_blank_L sig n i  ⊨ R_move_to_blank_L sig n i.
#sig #n #i 
@(sem_seq_app ?????? 
  (ssem_move_until_L ? (not_blank sig n i)) (sem_extend ? (all_blanks sig n)))
#tin #tout * #t1 * * #Ht1a #Ht1b * #Ht2a #Ht2b %
  [#Hcur >(Ht1a Hcur) in Ht2a; /2 by /
  |#ls #a #rs #Htin #Hreg #Hreg2 -Ht1a cases (Ht1b … Htin)
    [* #Hnb #Ht1 -Ht1b -Ht2a >Ht1 in Ht2b; >Htin #H 
     %{a} %{[ ]} %{ls} 
     %[%[%[%[%[@Hreg|@Hreg2]|@Hnb]|//]|//]|@H normalize % #H1 destruct (H1)]
    |* 
    [(* we find the blank *)
     * #ls1 * #b * #ls2 * * * #H1 #H2 #H3 #Ht1
     >Ht1 in Ht2b; #Hout -Ht1b
     %{b} %{(a::ls1)} %{ls2} 
     %[%[%[%[%[>H1 in Hreg; #H @H 
              |#j #jneqi whd in match (hd ???); whd in match (tail ??);
               <H1 @(Hreg2 j jneqi)]|@H2] |//]|>H1 //]
      |@Hout normalize % normalize #H destruct (H)
      ]
    |* #b * #lss * * #H1 #H2 #Ht1 -Ht1b >Ht1 in Ht2a; 
     whd in match (left ??); whd in match (right ??); #Hout
     %{(all_blanks …)} %{(lss@[b])} %{[]}
     %[%[%[%[%[<H2 @regular_extend // 
              |<H2 #j #jneqi whd in match (hd ???); whd in match (tail ??); 
               @regular_trace_extl @Hreg2 //]
            |whd in match (not_blank ????); >blank_all_blanks //]
          |<H2 //]
        |#j #lejn <H2 @sym_eq @to_blank_i_ext]
      |>reverse_append >reverse_single @Hout normalize // 
      ]
    ]
  ]
qed.

(******************************************************************************)
   
definition shift_i_L ≝ λsig,n,i.
   ncombf_r (multi_sig …) (shift_i sig n i) (all_blanks sig n) ·
   mti sig n i · 
   extend ? (all_blanks sig n).
   
definition R_shift_i_L ≝ λsig,n,i,t1,t2.
    (∀a,ls,rs. 
      t1 = midtape ? ls a rs  → 
      ((∃rs1,b,rs2,a1,rss.
        rs = rs1@b::rs2 ∧ 
        nth i ? (vec … b) (blank ?) = (blank ?) ∧
        (∀x. mem ? x rs1 → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs1) (a1::rss) ∧
        t2 = midtape (multi_sig sig n) ((reverse ? (a1::rss))@ls) b rs2) ∨
      (∃b,rss. 
        (∀x. mem ? x rs → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs) (rss@[b]) ∧
        t2 = midtape (multi_sig sig n) 
          ((reverse ? (rss@[b]))@ls) (all_blanks sig n) [ ]))).

definition R_shift_i_L_new ≝ λsig,n,i,t1,t2.
  (∀a,ls,rs. 
   t1 = midtape ? ls a rs  → 
   ∃rs1,b,rs2,rss.
      b = hd ? rs2 (all_blanks sig n) ∧
      nth i ? (vec … b) (blank ?) = (blank ?) ∧
      rs = rs1@rs2 ∧ 
      (∀x. mem ? x rs1 → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
      shift_l sig n i (a::rs1) rss ∧
      t2 = midtape (multi_sig sig n) ((reverse ? rss)@ls) b (tail ? rs2)). 
          
theorem sem_shift_i_L: ∀sig,n,i. shift_i_L sig n i  ⊨ R_shift_i_L sig n i.
#sig #n #i 
@(sem_seq_app ?????? 
  (sem_ncombf_r (multi_sig sig n) (shift_i sig n i)(all_blanks sig n))
   (sem_seq ????? (ssem_mti sig n i) 
    (sem_extend ? (all_blanks sig n))))
#tin #tout * #t1 * * #Ht1a #Ht1b * #t2 * * #Ht2a #Ht2b * #Htout1 #Htout2
#a #ls #rs cases rs
  [#Htin %2 %{(shift_i sig n i a (all_blanks sig n))} %{[ ]} 
   %[%[#x @False_ind | @daemon]
    |lapply (Ht1a … Htin) -Ht1a -Ht1b #Ht1 
     lapply (Ht2a … Ht1) -Ht2a -Ht2b #Ht2 >Ht2 in Htout1; 
     >Ht1 whd in match (left ??); whd in match (right ??); #Htout @Htout // 
    ]
  |#a1 #rs1 #Htin 
   lapply (Ht1b … Htin) -Ht1a -Ht1b #Ht1 
   lapply (Ht2b … Ht1) -Ht2a -Ht2b *
    [(* a1 is blank *) * #H1 #H2 %1
     %{[ ]} %{a1} %{rs1} %{(shift_i sig n i a a1)} %{[ ]}
     %[%[%[%[// |//] |#x @False_ind] | @daemon]
      |>Htout2 [>H2 >reverse_single @Ht1 |>H2 >Ht1 normalize % #H destruct (H)]
      ]
    |*
    [* #rs10 * #b * #rs2 * #rss * * * * #H1 #H2 #H3 #H4
     #Ht2 %1 
     %{(a1::rs10)} %{b} %{rs2} %{(shift_i sig n i a a1)} %{rss}
     %[%[%[%[>H1 //|//] |@H3] |@daemon ]
      |>reverse_cons >associative_append 
       >H2 in Htout2; #Htout >Htout [@Ht2| >Ht2 normalize % #H destruct (H)]  
      ]
    |* #b * #rss * * #H1 #H2 
     #Ht2 %2
     %{(shift_i sig n i b (all_blanks sig n))} %{(shift_i sig n i a a1::rss)}
     %[%[@H1 |@daemon ]
      |>Ht2 in Htout1; #Htout >Htout //
       whd in match (left ??); whd in match (right ??);
       >reverse_append >reverse_single >associative_append  >reverse_cons
       >associative_append // 
       ]
     ]
   ]
 ]
qed.
 
theorem sem_shift_i_L_new: ∀sig,n,i. 
  shift_i_L sig n i  ⊨ R_shift_i_L_new sig n i.
#sig #n #i 
@(Realize_to_Realize … (sem_shift_i_L sig n i))
#t1 #t2 #H #a #ls #rs #Ht1 lapply (H a ls rs Ht1) *
  [* #rs1 * #b * #rs2 * #a1 * #rss * * * * #H1 #H2 #H3 #H4 #Ht2
   %{rs1} %{b} %{(b::rs2)} %{(a1::rss)} 
   %[%[%[%[%[//|@H2]|@H1]|@H3]|@H4] | whd in match (tail ??); @Ht2]
  |* #b * #rss * * #H1 #H2 #Ht2
   %{rs} %{(all_blanks sig n)} %{[]} %{(rss@[b])} 
   %[%[%[%[%[//|@blank_all_blanks]|//]|@H1]|@H2] | whd in match (tail ??); @Ht2]
  ]
qed.
   

(*******************************************************************************
The following machine implements a full move for a trace: we reach the left 
border, shift the i-th trace and come back to the head position. 
The head may hold additional information A, so we suppose that the tape alphabet
is the disjoint sum between A and the alphabet sig of the multi tape machine. *) 

definition TA ≝ λA,sig. FinSum A sig.
definition MTA ≝ λA,sig,n.multi_sig (TA A sig) n.

definition is_head ≝ λA,sig.λc:sig_ext (TA A sig).
  match c with
  [ None ⇒ false
  | Some a ⇒ match a with 
     [ inl _ ⇒ true
     | inr _ ⇒ false]].

definition is_sig ≝ λA,sig.λc:sig_ext (TA A sig).
  match c with
  [ None ⇒ false
  | Some a ⇒ match a with 
     [ inl _ ⇒ false
     | inr _ ⇒ true]].

definition not_head ≝ λA,sig,n.λc:multi_sig (TA A sig) (S n).
  ¬(is_head A sig (nth n ? (vec … c) (blank ?))).
  
lemma not_head_all_blanks : ∀A,sig,n. 
  not_head A sig n (all_blanks … (S n)) = true.
#A #sig #n whd in ⊢ (??%?); >blank_all_blanks //
qed.  

definition no_head_in ≝ λA,sig,n,l. 
  ∀x. mem ? x (trace (TA A sig) (S n) n l) → is_head … x = false.

(*
lemma not_head_true: ∀A,sig,n,c. not_head A sig n c = true → 
  is_head … (nth n ? (vec … c) (blank ?)) = false.
*)

lemma hd_nil : ∀A,d. hd A [ ] d = d. 
// qed.

definition mtiL ≝ λA,sig,n,i.
   move_to_blank_L (TA A sig) (S n) i · 
   shift_i_L (TA A sig) (S n) i ·
   move_until ? L (not_head A sig n). 
   
definition Rmtil ≝ λA,sig,n,i,t1,t2.
  ∀ls,a,rs. 
   t1 = midtape (MTA A sig (S n)) ls a rs → 
   is_head A sig (nth n ? (vec … a) (blank ?)) = true →  
   (∀i.regular_trace (TA A sig) (S n) a ls rs i) → 
   (* next: we cannot be on rightof on trace i *)
   (nth i ? (vec … a) (blank ?) = (blank ?) 
     → nth i ? (vec … (hd ? rs (all_blanks …))) (blank ?) ≠ (blank ?)) →
   no_head_in … ls →   
   no_head_in … rs  → 
   (∃ls1,a1,rs1.
     t2 = midtape (MTA A sig (S n)) ls1 a1 rs1 ∧
     (∀i.regular_trace … a1 ls1 rs1 i) ∧
     (∀j. j ≤ n → j ≠ i → to_blank_i ? (S n) j (a1::ls1) = to_blank_i ? (S n) j (a::ls)) ∧
     (∀j. j ≤ n → j ≠ i → to_blank_i ? (S n) j rs1 = to_blank_i ? (S n) j rs) ∧
     (to_blank_i ? (S n) i ls1 = to_blank_i ? (S n) i (a::ls)) ∧
     (to_blank_i ? (S n) i (a1::rs1)) = to_blank_i ? (S n) i rs).

theorem sem_Rmtil: ∀A,sig,n,i. i < n → mtiL A sig n i  ⊨ Rmtil A sig n i.
#A #sig #n #i #lt_in
@(sem_seq_app ?????? 
  (sem_move_to_blank_L … )
   (sem_seq ????? (sem_shift_i_L_new …)
    (ssem_move_until_L ? (not_head A sig n))))
#tin #tout * #t1 * * #_ #Ht1 * #t2 * #Ht2 * #_ #Htout
(* we start looking into Rmitl *)
#ls #a #rs #Htin (* tin is a midtape *)
#Hheada #Hreg #no_rightof #Hnohead_ls #Hnohead_rs 
cut (regular_i ? (S n) (a::ls) i)
  [cases (Hreg i) * // 
   cases (true_or_false (nth i ? (vec … a) (blank ?) == (blank ?))) #Htest
    [#_ @daemon (* absurd, since hd rs non e' blank *)
    |#H #_ @daemon]] #Hreg1
lapply (Ht1 … Htin Hreg1 ?) [#j #_ @Hreg] -Ht1 -Htin
* #b * #ls1 * #ls2 * * * * * #reg_ls1_i #reg_ls1_j #Hno_blankb #Hhead #Hls1 #Ht1
lapply (Ht2 … Ht1) -Ht2 -Ht1 
* #rs1 * #b0 * #rs2 * #rss * * * * * #Hb0 #Hb0blank #Hrs1 #Hrs1b #Hrss #Ht2
(* we need to recover the position of the head of the emulated machine
   that is the head of ls1. This is somewhere inside rs1 *) 
cut (∃rs11. rs1 = (reverse ? ls1)@rs11)
  [cut (ls1 = [ ] ∨ ∃aa,tlls1. ls1 = aa::tlls1)
    [cases ls1 [%1 // | #aa #tlls1 %2 %{aa} %{tlls1} //]] *
      [#H1ls1 %{rs1} >H1ls1 //
      |* #aa * #tlls1 #H1ls1 >H1ls1 in Hrs1; 
       cut (aa = a) [>H1ls1 in Hls1; #H @(to_blank_hd … H)] #eqaa >eqaa  
       #Hrs1_aux cases (compare_append … (sym_eq … Hrs1_aux)) #l *
        [* #H1 #H2 %{l} @H1
        |(* this is absurd : if l is empty, the case is as before.
           if l is not empty then it must start with a blank, since it is the
           first character in rs2. But in this case we would have a blank 
           inside ls1=a::tls1 that is absurd *)
          @daemon
        ]]]   
   * #rs11 #H1
cut (rs = rs11@rs2)
  [@(injective_append_l … (reverse … ls1)) >Hrs1 <associative_append <H1 //] #H2
lapply (Htout … Ht2) -Htout -Ht2 *
  [(* the current character on trace i holds the head-mark.
      The case is absurd, since b0 is the head of rs2, that is a sublist of rs, 
      and the head-mark is not in rs *)
   * #H3 @False_ind @(absurd (true=false)) [2://] <H3 @sym_eq
   <(notb_notb true) @(eq_f … notb) @Hnohead_rs >H2 >trace_append @mem_append_l2 
   lapply Hb0 cases rs2 
    [>hd_nil #H >H in H3; >not_head_all_blanks #Habs destruct (Habs)
    |#c #r #H4 %1 >H4 //
    ]
  |* 
  [(* we reach the head position *)
   (* cut (trace sig n j (a1::ls20)=trace sig n j (ls1@b::ls2)) *)
   * #ls10 * #a1 * #ls20 * * * #Hls20 #Ha1 #Hnh #Htout
   cut (∀j.j ≠ i →
      trace ? (S n) j (reverse (multi_sig (TA A sig) (S n)) rs1@b::ls2) = 
      trace ? (S n) j (ls10@a1::ls20))
    [#j #ineqj >append_cons <reverse_cons >trace_def <map_append <reverse_map
     lapply (trace_shift_neq … (le_S … lt_in) ? (sym_not_eq … ineqj) … Hrss) [//] #Htr
     <(trace_def …  (b::rs1)) <Htr >reverse_map >map_append @eq_f @Hls20 ] 
   #Htracej
   cut (trace ? (S n) i (reverse (multi_sig (TA A sig) (S n)) (rs1@[b0])@ls2) = 
        trace ? (S n) i (ls10@a1::ls20))
    [>trace_def <map_append <reverse_map <map_append <(trace_def … [b0]) 
     cut (trace ? (S n) i [b0] = [blank ?]) [@daemon] #Hcut >Hcut
     lapply (trace_shift … (le_S … lt_in) … Hrss) [//] whd in match (tail ??); #Htr <Htr
     >reverse_map >map_append <trace_def <Hls20 % 
    ] 
   #Htracei
   cut (∀j. j ≠ i →
      (trace ? (S n) j (reverse (MTA A sig (S n)) rs11) = trace ? (S n) j ls10) ∧ 
      (trace ? (S n) j (ls1@b::ls2) = trace ? (S n) j (a1::ls20)))
   [@daemon (* si fa 
     #j #ineqj @(first_P_to_eq ? (λx. x ≠ head ?))
      [lapply (Htracej … ineqj) >trace_def in ⊢ (%→?); <map_append 
       >trace_def in ⊢ (%→?); <map_append #H @H  
      | *) ] #H2
  cut ((trace ? (S n) i (b0::reverse ? rs11) = trace ? (S n) i (ls10@[a1])) ∧ 
      (trace ? (S n) i (ls1@ls2) = trace ? (S n) i ls20))
   [>H1 in Htracei; >reverse_append >reverse_single >reverse_append 
     >reverse_reverse >associative_append >associative_append
     @daemon
    ] #H3    
  cut (∀j. j ≠ i → 
    trace ? (S n) j (reverse ? ls10@rs2) = trace ? (S n) j rs)
    [#j #jneqi @(injective_append_l … (trace ? (S n) j (reverse ? ls1)))
     >map_append >map_append >Hrs1 >H1 >associative_append 
     <map_append <map_append in ⊢ (???%); @eq_f 
     <map_append <map_append @eq_f2 // @sym_eq 
     <(reverse_reverse … rs11) <reverse_map <reverse_map in ⊢ (???%);
     @eq_f @(proj1 … (H2 j jneqi))] #Hrs_j
   %{ls20} %{a1} %{(reverse ? (b0::ls10)@tail ? rs2)}
   %[%[%[%[%[@Htout
    |#j cases (decidable_eq_nat j i)
      [#eqji >eqji (* by cases wether a1 is blank *)
       @daemon
      |#jneqi lapply (reg_ls1_j … jneqi) #H4 
       >reverse_cons >associative_append >Hb0 @regular_cons_hd_rs
       @(eq_trace_to_regular … H4)
        [<hd_trace >(proj2 … (H2 … jneqi)) >hd_trace %
        |<tail_trace >(proj2 … (H2 … jneqi)) >tail_trace %
        |@sym_eq @Hrs_j //
        ]
      ]]
    |#j #lejn #jneqi <(Hls1 … (le_S_S … lejn)) 
     >to_blank_i_def >to_blank_i_def @eq_f @sym_eq @(proj2 … (H2 j jneqi))]
    |#j #lejn #jneqi >reverse_cons >associative_append >Hb0
     <to_blank_hd_cons >to_blank_i_def >to_blank_i_def @eq_f @Hrs_j //]
    |<(Hls1 i) [2:@le_S //] 
     lapply (all_blank_after_blank … reg_ls1_i) 
       [@(\P ?) @daemon] #allb_ls2
     whd in match (to_blank_i ????); <(proj2 … H3)
     @daemon ]
    |>reverse_cons >associative_append  
     cut (to_blank_i ? (S n) i rs = to_blank_i ? (S n) i (rs11@[b0])) [@daemon] 
     #Hcut >Hcut >(to_blank_i_chop  … b0 (a1::reverse …ls10)) [2: @Hb0blank]
     >to_blank_i_def >to_blank_i_def @eq_f 
     >trace_def >trace_def @injective_reverse >reverse_map >reverse_cons
     >reverse_reverse >reverse_map >reverse_append >reverse_single @sym_eq
     @(proj1 … H3)
    ]
  |(*we do not find the head: this is absurd *)
   * #b1 * #lss * * #H2 @False_ind 
   cut (∀x0. mem ? x0 (trace ? (S n) n (b0::reverse ? rss@ls2)) → is_head … x0 = false)
     [@daemon] -H2 #H2
   lapply (trace_shift_neq ? (S n) i n … (le_S … lt_in) … Hrss)
     [@lt_to_not_eq @lt_in | // ] 
   #H3 @(absurd 
        (is_head  … (nth n ? (vec … (hd ? (ls1@[b]) (all_blanks … (S n)))) (blank ?)) = true))
     [>Hhead //
     |@eqnot_to_noteq @H2 >trace_def %2 <map_append @mem_append_l1 <reverse_map <trace_def 
      >H3 >H1 >trace_def >reverse_map >reverse_cons >reverse_append 
      >reverse_reverse >associative_append <map_append @mem_append_l2
      cases ls1 [%1 % |#x #ll %1 %]
     ]
   ]
 ]
qed.
