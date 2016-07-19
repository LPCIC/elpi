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
include "turing/if_multi.ma".
include "turing/while_multi.ma".
include "turing/inject.ma".
include "turing/basic_multi_machines.ma".

(**************************** injected machines *******************************)

definition Rtc_multi_true ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
   (∃c. current alpha (nth i ? t1 (niltape ?)) = Some ? c ∧ test c = true) ∧ t2 = t1.
   
definition Rtc_multi_false ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
    (∀c. current alpha (nth i ? t1 (niltape ?)) = Some ? c → test c = false) ∧ t2 = t1.

lemma sem_test_char_multi :
  ∀alpha,test,n,i.i ≤ n → 
  inject_TM ? (test_char ? test) n i ⊨ 
  [ tc_true : Rtc_multi_true alpha test n i, Rtc_multi_false alpha test n i ].
#alpha #test #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_char alpha test) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * * #c *
  #Hcur #Htestc #Hnth_i #Hnth_j %
  [ %{c} % //
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
| #Hqfalse lapply (Hfalse Hqfalse) * * #Htestc #Hnth_i #Hnth_j %
  [ @Htestc
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
qed.

definition Rm_test_null_true ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
   current alpha (nth i ? t1 (niltape ?)) ≠ None ? ∧ t2 = t1.
   
definition Rm_test_null_false ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
    current alpha (nth i ? t1 (niltape ?)) = None ? ∧ t2 = t1.

lemma sem_test_null_multi : ∀alpha,n,i.i ≤ n → 
  inject_TM ? (test_null ?) n i ⊨ 
    [ tc_true : Rm_test_null_true alpha n i, Rm_test_null_false alpha n i ].
#alpha #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_null alpha) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * #Hcur #Hnth_i #Hnth_j % //
  @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) #Hi0i
  [ >Hi0i @sym_eq @Hnth_i | @sym_eq @Hnth_j @sym_not_eq // ] ] 
| #Hqfalse lapply (Hfalse Hqfalse) * * #Hcur #Hnth_i #Hnth_j %
  [ @Hcur
  | @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) // 
    #Hi0i @sym_eq @Hnth_j @sym_not_eq // ] ] 
qed.

(* move a single tape *)
definition mmove ≝ λi,sig,n,D.inject_TM sig (move sig D) n i.

definition Rm_multi ≝ 
  λalpha,n,i,D.λt1,t2:Vector ? (S n).
  t2 = change_vec ? (S n) t1 (tape_move alpha (nth i ? t1 (niltape ?)) D) i.

lemma sem_move_multi :
  ∀alpha,n,i,D.i ≤ n → 
  mmove i alpha n D ⊨ Rm_multi alpha n i D.
#alpha #n #i #D #Hin #ta cases (sem_inject … Hin (sem_move_single alpha D) ta)
#k * #outc * #Hloop * whd in ⊢ (%→?); #Htb1 #Htb2 %{k} %{outc} % [ @Hloop ]
whd @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) #Hi0i
[ >Hi0i >Htb1 >nth_change_vec //
| >nth_change_vec_neq [|@sym_not_eq //] <Htb2 // @sym_not_eq // ]
qed.

(********************** look_ahead test *************************)

definition mtestR ≝ λsig,i,n,test.
  (mmove i sig n R) · 
    (ifTM ?? (inject_TM ? (test_char ? test) n i)
    (single_finalTM ?? (mmove i sig n L))
    (mmove i sig n L) tc_true).


(* underspecified *)
definition RmtestR_true ≝ λsig,i,n,test.λt1,t2:Vector ? n.
  ∀ls,c,c1,rs.
    nth i ? t1 (niltape ?) = midtape sig ls c (c1::rs) →
    t1 = t2 ∧ (test c1 = true).

definition RmtestR_false ≝ λsig,i,n,test.λt1,t2:Vector ? n.
  ∀ls,c,c1,rs.
    nth i ? t1 (niltape ?) = midtape sig ls c (c1::rs) →
    t1 = t2 ∧ (test c1 = false).   
    
definition mtestR_acc: ∀sig,i,n,test.states ?? (mtestR sig i n test). 
#sig #i #n #test @inr @inr @inl @inr @start_nop 
qed.

lemma sem_mtestR: ∀sig,i,n,test. i ≤ n →
  mtestR sig i n test ⊨ 
    [mtestR_acc sig i n test: 
       RmtestR_true sig  i (S n) test, RmtestR_false sig i (S n) test].
#sig #i #n #test #Hlein
@(acc_sem_seq_app sig n … (sem_move_multi … R Hlein)
   (acc_sem_if sig n ????????
     (sem_test_char_multi sig test n i Hlein)
     (sem_move_multi … L Hlein)
     (sem_move_multi … L Hlein)))
  [#t1 #t2 #t3 whd in ⊢ (%→?); #Hmove * #tx * whd in  ⊢ (%→?); * *
   #cx #Hcx #Htx #Ht2 #ls #c #c1 #rs #Ht1
   >Ht1 in Hmove; whd in match (tape_move ???); #Ht3 
   >Ht3 in Hcx; >nth_change_vec [|@le_S_S //] * whd in ⊢ (??%?→?);
   #Hsome destruct (Hsome) #Htest % [2:@Htest]
   >Htx in Ht2; whd in ⊢ (%→?); #Ht2 @(eq_vec … (niltape ?))
   #j #lejn cases (true_or_false (eqb i j)) #Hij
    [lapply lejn <(eqb_true_to_eq … Hij) #lein >Ht2 >nth_change_vec [2://]
     >Ht3 >nth_change_vec >Ht1 // 
    |lapply (eqb_false_to_not_eq … Hij) #Hneq >Ht2 >nth_change_vec_neq [2://]
     >Ht3 >nth_change_vec_neq //
    ]
  |#t1 #t2 #t3 whd in ⊢ (%→?); #Hmove * #tx * whd in  ⊢ (%→?); *
   #Hcx #Heqtx #Htx #ls #c #c1 #rs #Ht1
   >Ht1 in Hmove; whd in match (tape_move ???); #Ht3 
   >Ht3 in Hcx; >nth_change_vec [2:@le_S_S //] #Hcx lapply (Hcx ? (refl ??)) 
   #Htest % // @(eq_vec … (niltape ?))
   #j #lejn cases (true_or_false (eqb i j)) #Hij
    [lapply lejn <(eqb_true_to_eq … Hij) #lein >Htx >nth_change_vec [2://]
     >Heqtx >Ht3 >nth_change_vec >Ht1 // 
    |lapply (eqb_false_to_not_eq … Hij) #Hneq >Htx >nth_change_vec_neq [2://]
     >Heqtx >Ht3 >nth_change_vec_neq //
    ]
  ]
qed.
(* advance in parallel along two tapes src and dst until we reach the end
   of one tape *)

definition parmove ≝ λsrc,dst,sig,n,D.
  whileTM … (parmove_step src dst sig n D) parmove1.

definition R_parmoveL ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  (∀x,xs,rs.
    nth src ? int (niltape ?) = midtape sig xs x rs → 
    ∀ls0,x0,target,rs0.|xs| = |target| → 
    nth dst ? int (niltape ?) = midtape sig (target@ls0) x0 rs0 → 
    outt = change_vec ?? 
           (change_vec ?? int (mk_tape sig [] (None ?) (reverse ? xs@x::rs)) src)
           (mk_tape sig (tail ? ls0) (option_hd ? ls0) (reverse ? target@x0::rs0)) dst) ∧
  (∀x,xs,rs.
    nth dst ? int (niltape ?) = midtape sig xs x rs → 
    ∀ls0,x0,target,rs0.|xs| = |target| → 
    nth src ? int (niltape ?) = midtape sig (target@ls0) x0 rs0 → 
    outt = change_vec ?? 
           (change_vec ?? int (mk_tape sig [] (None ?) (reverse ? xs@x::rs)) dst)
           (mk_tape sig (tail ? ls0) (option_hd ? ls0) (reverse ? target@x0::rs0)) src) ∧
  ((current ? (nth src ? int (niltape ?)) = None ? ∨
    current ? (nth dst ? int (niltape ?)) = None ?) →
    outt = int).
  
lemma wsem_parmoveL : ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  parmove src dst sig n L ⊫ R_parmoveL src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_parmove_step src dst sig n L Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ whd in ⊢ (%→?); * #H #Houtc % [2: #_ @Houtc ] cases H #Hcurtb
  [ % 
    [ #x #xs #rs #Hsrctb >Hsrctb in Hcurtb; normalize in ⊢ (%→?);
      #Hfalse destruct (Hfalse)
    | #x #xs #rs #Hdsttb #ls0 #x0 #target #rs0 #Hlen #Hsrctb >Hsrctb in Hcurtb;
      normalize in ⊢ (%→?); #H destruct (H)
    ]
  | %
    [ #x #xs #rs #Hsrctb #ls0 #x0 #target 
      #rs0 #Hlen #Hdsttb >Hdsttb in Hcurtb; normalize in ⊢ (%→?); #H destruct (H)
    | #x #xs #rs #Hdsttb >Hdsttb in Hcurtb; normalize in ⊢ (%→?);
      #Hfalse destruct (Hfalse)
    ]
  ]  
| #td #te * #c0 * #c1 * * #Hc0 #Hc1 #Hd #Hstar #IH #He 
  lapply (IH He) -IH * * #IH1a #IH1b #IH2 % [ %
  [ #x #xs #rs #Hsrc_td #ls0 #x0 #target
    #rs0 #Hlen #Hdst_td
    >Hsrc_td in Hc0; normalize in ⊢ (%→?); #Hc0 destruct (Hc0)
    >Hdst_td in Hd; >Hsrc_td @(list_cases2 … Hlen)
    [ #Hxsnil #Htargetnil >Hxsnil >Htargetnil #Hd >IH2 
      [2: %1 >Hd >nth_change_vec_neq [|@(sym_not_eq … Hneq)]
      >nth_change_vec //]  
      >Hd -Hd @(eq_vec … (niltape ?))
      #i #Hi cases (decidable_eq_nat i src) #Hisrc
      [ >Hisrc >(nth_change_vec_neq … src dst) [|@(sym_not_eq … Hneq)]
        >nth_change_vec //
        >(nth_change_vec_neq … src dst) [|@(sym_not_eq … Hneq)]
        >nth_change_vec //
      | cases (decidable_eq_nat i dst) #Hidst
        [ >Hidst >nth_change_vec // >nth_change_vec //
          >Hdst_td in Hc1; >Htargetnil
          normalize in ⊢ (%→?); #Hc1 destruct (Hc1) cases ls0 //
        | >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
          >nth_change_vec_neq [|@(sym_not_eq … Hisrc)]
          >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
          >nth_change_vec_neq [|@(sym_not_eq … Hisrc)] % 
        ]
      ]
    | #hd1 #hd2 #tl1 #tl2 #Hxs #Htarget >Hxs >Htarget #Hd
      >(IH1a hd1 tl1 (c0::rs) ? ls0 hd2 tl2 (x0::rs0))
      [ >Hd >(change_vec_commute … ?? td ?? src dst) //
        >change_vec_change_vec
        >(change_vec_commute … ?? td ?? dst src) [|@sym_not_eq //]
        >change_vec_change_vec
        >reverse_cons >associative_append
        >reverse_cons >associative_append % 
      | >Hd >nth_change_vec //
      | >Hxs in Hlen; >Htarget normalize #Hlen destruct (Hlen) //
      | >Hd >nth_change_vec_neq [|@sym_not_eq //]
        >nth_change_vec // ]
    ]
  | #x #xs #rs #Hdst_td #ls0 #x0 #target
    #rs0 #Hlen #Hsrc_td
    >Hdst_td in Hc0; normalize in ⊢ (%→?); #Hc0 destruct (Hc0)
    >Hsrc_td in Hd; >Hdst_td @(list_cases2 … Hlen)
    [ #Hxsnil #Htargetnil >Hxsnil >Htargetnil #Hd >IH2 
      [2: %2 >Hd >nth_change_vec //]
      >Hd -Hd @(eq_vec … (niltape ?))
      #i #Hi cases (decidable_eq_nat i dst) #Hidst
      [ >Hidst >(nth_change_vec_neq … dst src) //
        >nth_change_vec // >nth_change_vec //
      | cases (decidable_eq_nat i src) #Hisrc
        [ >Hisrc >nth_change_vec // >(nth_change_vec_neq …) [|@sym_not_eq //]
          >Hsrc_td in Hc1; >Htargetnil
          normalize in ⊢ (%→?); #Hc1 destruct (Hc1) >nth_change_vec //
          cases ls0 //
        | >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
          >nth_change_vec_neq [|@(sym_not_eq … Hisrc)]
          >nth_change_vec_neq [|@(sym_not_eq … Hisrc)]
          >nth_change_vec_neq [|@(sym_not_eq … Hidst)] % 
        ]
      ]
    | #hd1 #hd2 #tl1 #tl2 #Hxs #Htarget >Hxs >Htarget #Hd
      >(IH1b hd1 tl1 (x::rs) ? ls0 hd2 tl2 (x0::rs0))
      [ >Hd >(change_vec_commute … ?? td ?? dst src) [|@sym_not_eq //]
        >change_vec_change_vec
        >(change_vec_commute … ?? td ?? src dst) //
        >change_vec_change_vec
        >reverse_cons >associative_append
        >reverse_cons >associative_append
        >change_vec_commute [|@sym_not_eq //] %
      | >Hd >nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec //
      | >Hxs in Hlen; >Htarget normalize #Hlen destruct (Hlen) //
      | >Hd >nth_change_vec // ]
    ]
  ]
| >Hc0 >Hc1 * [ #Hc0 destruct (Hc0) | #Hc1 destruct (Hc1) ]
] ]
qed.
 
lemma terminate_parmoveL :  ∀src,dst,sig,n,t.
  src ≠ dst → src < S n → dst < S n → 
  parmove src dst sig n L ↓ t.
#src #dst #sig #n #t #Hneq #Hsrc #Hdst
@(terminate_while … (sem_parmove_step …)) //
<(change_vec_same … t src (niltape ?))
cases (nth src (tape sig) t (niltape ?))
[ % #t1 * #x1 * #x2 * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct 
|2,3: #a0 #al0 % #t1 * #x1 * #x2 * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls lapply t -t elim ls
  [#t #c #rs % #t1 * #x1 * #x2 * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #Hcurdst >change_vec_change_vec #Ht1 % 
   #t2 * #y1 * #y2 * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#l0 #ls0 #IH #t #c #rs % #t1 * #x1 * #x2 * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcurdst
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_parmoveL : ∀src,dst,sig,n.
  src ≠ dst → src < S n → dst < S n → 
  parmove src dst sig n L ⊨ R_parmoveL src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst @WRealize_to_Realize 
[/2/ | @wsem_parmoveL //]
qed.

(* compare *)
definition compare ≝ λi,j,sig,n.
  whileTM … (compare_step i j sig n) comp1.

(*    (∃rs'.rs = rs0@rs' ∧ current ? (nth j ? outt (niltape ?)) = None ?) ∨
    (∃rs0'.rs0 = rs@rs0' ∧ 
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs@x::ls) (None sig) []) i)
            (mk_tape sig (reverse sig rs@x::ls0) (option_hd sig rs0')
            (tail sig rs0')) j) ∨
    (∃xs,ci,cj,rs',rs0'.ci ≠ cj ∧ rs = xs@ci::rs' ∧ rs0 = xs@cj::rs0' ∧
     outt = change_vec ?? 
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs') i)
            (midtape sig (reverse ? xs@x::ls0) cj rs0') j)).*)
definition R_compare ≝ 
  λi,j,sig,n.λint,outt: Vector (tape sig) (S n).
  ((current ? (nth i ? int (niltape ?)) ≠ current ? (nth j ? int (niltape ?)) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,rs,ls0,rs0. 
(*    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) → *)
    nth i ? int (niltape ?) = midtape sig ls x rs →
    nth j ? int (niltape ?) = midtape sig ls0 x rs0 →
    (∃rs'.rs = rs0@rs' ∧ 
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs0@x::ls) (option_hd sig rs') (tail ? rs')) i)
            (mk_tape sig (reverse sig rs0@x::ls0) (None ?) [ ]) j) ∨
    (∃rs0'.rs0 = rs@rs0' ∧ 
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs@x::ls) (None sig) []) i)
            (mk_tape sig (reverse sig rs@x::ls0) (option_hd sig rs0')
            (tail sig rs0')) j) ∨
    (∃xs,ci,cj,rs',rs0'.ci ≠ cj ∧ rs = xs@ci::rs' ∧ rs0 = xs@cj::rs0' ∧
     outt = change_vec ?? 
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs') i)
            (midtape sig (reverse ? xs@x::ls0) cj rs0') j)).            
          
lemma wsem_compare : ∀i,j,sig,n.i ≠ j → i < S n → j < S n → 
  compare i j sig n ⊫ R_compare i j sig n.
#i #j #sig #n #Hneq #Hi #Hj #ta #k #outc #Hloop
lapply (sem_while … (sem_comp_step i j sig n Hneq Hi Hj) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ whd in ⊢ (%→?); * * [ *
 [ #Hcicj #Houtc % 
   [ #_ @Houtc
   | #ls #x #rs #ls0 #rs0 #Hnthi #Hnthj
     >Hnthi in Hcicj; >Hnthj normalize in ⊢ (%→?); * #H @False_ind @H %
   ]
 | #Hci #Houtc %
   [ #_ @Houtc
   | #ls #x #rs #ls0 #rs0 #Hnthi >Hnthi in Hci;
     normalize in ⊢ (%→?); #H destruct (H) ] ]
 | #Hcj #Houtc %
  [ #_ @Houtc
  | #ls #x #rs #ls0 #rs0 #_ #Hnthj >Hnthj in Hcj;
    normalize in ⊢ (%→?); #H destruct (H) ] ]
| #td #te * #x * * #Hci #Hcj #Hd #Hstar #IH #He lapply (IH He) -IH *
  #IH1 #IH2 %
  [ >Hci >Hcj * [ * 
    [ * #H @False_ind @H % | #H destruct (H)] | #H destruct (H)] 
  | #ls #c0 #rs #ls0 #rs0 cases rs
    [ -IH2 #Hnthi #Hnthj % %2 %{rs0} % [%]
      >Hnthi in Hd; #Hd >Hd in IH1; #IH1 >IH1
      [| % %2 >nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec // % ]
      >Hnthj cases rs0 [| #r1 #rs1 ] %
    | #r1 #rs1 #Hnthi cases rs0
      [ -IH2 #Hnthj % % %{(r1::rs1)} % [%]
        >Hnthj in Hd; #Hd >Hd in IH1; #IH1 >IH1
        [| %2 >nth_change_vec // ]
        >Hnthi >Hnthj %
      | #r2 #rs2 #Hnthj lapply IH2; >Hd in IH1; >Hnthi >Hnthj
        >nth_change_vec //
        >nth_change_vec_neq [| @sym_not_eq // ] >nth_change_vec //
        cases (true_or_false (r1 == r2)) #Hr1r2
        [ >(\P Hr1r2) #_ #IH2 cases (IH2 … (refl ??) (refl ??)) [ *
          [ * #rs' * #Hrs1 #Hcurout_j % % %{rs'}
            >Hrs1 % 
            [ % 
            | >Hcurout_j >change_vec_commute // >change_vec_change_vec
              >change_vec_commute // @sym_not_eq // ]
          | * #rs0' * #Hrs2 #Hcurout_i % %2 %{rs0'}
            >Hrs2 >Hcurout_i % //
            >change_vec_commute // >change_vec_change_vec
            >change_vec_commute [|@sym_not_eq//] >change_vec_change_vec
            >reverse_cons >associative_append >associative_append % ]
          | * #xs * #ci * #cj * #rs' * #rs0' * * * #Hcicj #Hrs1 #Hrs2 
            >change_vec_commute // >change_vec_change_vec 
            >change_vec_commute [| @sym_not_eq ] // >change_vec_change_vec 
            #Houtc %2 %{(r2::xs)} %{ci} %{cj} %{rs'} %{rs0'}
            % [ % [ % [ // | >Hrs1 // ] | >Hrs2 // ] 
              | >reverse_cons >associative_append >associative_append >Houtc % ] ]
        | lapply (\Pf Hr1r2) -Hr1r2 #Hr1r2 #IH1 #_ %2
          >IH1 [| % % normalize @(not_to_not … Hr1r2) #H destruct (H) % ]
          %{[]} %{r1} %{r2} %{rs1} %{rs2} % [ % [ % /2/ | % ] | % ] ]]]]]
qed.
 
lemma terminate_compare :  ∀i,j,sig,n,t.
  i ≠ j → i < S n → j < S n → 
  compare i j sig n ↓ t.
#i #j #sig #n #t #Hneq #Hi #Hj
@(terminate_while … (sem_comp_step …)) //
<(change_vec_same … t i (niltape ?))
cases (nth i (tape sig) t (niltape ?))
[ % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
|2,3: #a0 #al0 % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls #c #rs lapply c -c lapply ls -ls lapply t -t elim rs
  [#t #ls #c % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #_ >change_vec_change_vec #Ht1 % 
   #t2 * #x0 * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#r0 #rs0 #IH #t #ls #c % #t1 * #x * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcur
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_compare : ∀i,j,sig,n.
  i ≠ j → i < S n → j < S n → 
  compare i j sig n ⊨ R_compare i j sig n.
#i #j #sig #n #Hneq #Hi #Hj @WRealize_to_Realize 
  [/2/| @wsem_compare // ]
qed.

(* copy *)

definition copy ≝ λsrc,dst,sig,n.
  whileTM … (copy_step src dst sig n) copy1.

definition R_copy ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ((current ? (nth src ? int (niltape ?)) = None ? ∨
    current ? (nth dst ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,x0,rs,ls0,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x rs →
    nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃rs01,rs02.rs0 = rs01@rs02 ∧ |rs01| = |rs| ∧
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs@x::ls) (None sig) []) src)
            (mk_tape sig (reverse sig rs@x::ls0) (option_hd sig rs02)
            (tail sig rs02)) dst) ∨
    (∃rs1,rs2.rs = rs1@rs2 ∧ |rs1| = |rs0| ∧
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs1@x::ls) (option_hd sig rs2)
            (tail sig rs2)) src)
            (mk_tape sig (reverse sig rs1@x::ls0) (None sig) []) dst)).

lemma wsem_copy : ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n ⊫ R_copy src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_copy_step src dst sig n Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ whd in ⊢ (%→?); * #Hnone #Hout %
  [#_ @Hout
  |#ls #x #x0 #rs #ls0 #rs0 #Hsrc1 #Hdst1 @False_ind cases Hnone
    [>Hsrc1 normalize #H destruct (H) | >Hdst1 normalize #H destruct (H)]
  ]
|#tc #td * #x * #y * * #Hcx #Hcy #Htd #Hstar #IH #He lapply (IH He) -IH *
 #IH1 #IH2 %
  [* [>Hcx #H destruct (H) | >Hcy #H destruct (H)]
  |#ls #x' #y' #rs #ls0 #rs0 #Hnth_src #Hnth_dst
   >Hnth_src in Hcx; whd in ⊢ (??%?→?); #H destruct (H)
   >Hnth_dst in Hcy; whd in ⊢ (??%?→?); #H destruct (H)
   >Hnth_src in Htd; >Hnth_dst -Hnth_src -Hnth_dst
   cases rs
    [(* the source tape is empty after the move *)
     #Htd lapply (IH1 ?) 
      [%1 >Htd >nth_change_vec_neq [2:@(not_to_not … Hneq) //] >nth_change_vec //]
     #Hout (* whd in match (tape_move ???); *) %1 %{([])} %{rs0} % 
      [% [// | // ] 
      |whd in match (reverse ??); whd in match (reverse ??);
       >Hout >Htd @eq_f2 // cases rs0 //
      ]
    |#c1 #tl1 cases rs0
      [(* the dst tape is empty after the move *)
       #Htd lapply (IH1 ?) [%2 >Htd >nth_change_vec //] 
       #Hout (* whd in match (tape_move ???); *) %2 %{[ ]} %{(c1::tl1)} % 
        [% [// | // ] 
        |whd in match (reverse ??); whd in match (reverse ??);
         >Hout >Htd @eq_f2 // 
        ]
      |#c2 #tl2 whd in match (tape_move_mono ???); whd in match (tape_move_mono ???);
       #Htd
       cut (nth src (tape sig) td (niltape sig)=midtape sig (x::ls) c1 tl1)
         [>Htd >nth_change_vec_neq [2:@(not_to_not … Hneq) //] @nth_change_vec //]
       #Hsrc_td
       cut (nth dst (tape sig) td (niltape sig)=midtape sig (x::ls0) c2 tl2)
         [>Htd @nth_change_vec //]
       #Hdst_td cases (IH2 … Hsrc_td Hdst_td) -Hsrc_td -Hdst_td
        [* #rs01 * #rs02 * * #H1 #H2 #H3 %1
         %{(c2::rs01)} %{rs02} % [% [@eq_f //|normalize @eq_f @H2]]
         >Htd in H3; >change_vec_commute // >change_vec_change_vec
         >change_vec_commute [2:@(not_to_not … Hneq) //] >change_vec_change_vec 
         #H >reverse_cons >associative_append >associative_append @H 
        |* #rs11 * #rs12 * * #H1 #H2 #H3 %2
         %{(c1::rs11)} %{rs12} % [% [@eq_f //|normalize @eq_f @H2]]
         >Htd in H3; >change_vec_commute // >change_vec_change_vec
         >change_vec_commute [2:@(not_to_not … Hneq) //] >change_vec_change_vec 
         #H >reverse_cons >associative_append >associative_append @H 
        ]
      ]
    ]
  ]
qed.
     
 
lemma terminate_copy :  ∀src,dst,sig,n,t.
  src ≠ dst → src < S n → dst < S n → copy src dst sig n ↓ t.
#src #dst #sig #n #t #Hneq #Hsrc #Hdts
@(terminate_while … (sem_copy_step …)) //
<(change_vec_same … t src (niltape ?))
cases (nth src (tape sig) t (niltape ?))
[ % #t1 * #x * #y * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
|2,3: #a0 #al0 % #t1 * #x * #y * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls #c #rs lapply c -c lapply ls -ls lapply t -t elim rs
  [#t #ls #c % #t1 * #x * #y * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #_ >change_vec_change_vec #Ht1 % 
   #t2 * #x0 * #y0 * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#r0 #rs0 #IH #t #ls #c % #t1 * #x * #y * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcur
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_copy : ∀src,dst,sig,n.
  src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n ⊨ R_copy src dst sig n.
#i #j #sig #n #Hneq #Hi #Hj @WRealize_to_Realize [/2/| @wsem_copy // ]
qed.
