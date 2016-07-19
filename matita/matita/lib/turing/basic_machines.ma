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

include "turing/while_machine.ma".

(******************* write a given symbol under the head **********************)
definition write_states ≝ initN 2.

definition wr0 : write_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition wr1 : write_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition write ≝ λalpha,c.
  mk_TM alpha write_states
  (λp.let 〈q,a〉 ≝ p in
    match pi1 … q with 
    [ O ⇒ 〈wr1,Some ? c,N〉
    | S _ ⇒ 〈wr1,None ?,N〉 ])
  wr0 (λx.x == wr1).
  
definition R_write ≝ λalpha,c,t1,t2.
  ∀ls,x,rs.t1 = midtape alpha ls x rs → t2 = midtape alpha ls c rs.
  
lemma sem_write : ∀alpha,c.Realize ? (write alpha c) (R_write alpha c).
#alpha #c #t @(ex_intro … 2) @ex_intro
  [|% [% |#ls #c #rs #Ht >Ht % ] ]
qed. 

definition R_write_strong ≝ λalpha,c,t1,t2.
  t2 = midtape alpha (left ? t1) c (right ? t1).
  
lemma sem_write_strong : ∀alpha,c.Realize ? (write alpha c) (R_write_strong alpha c).
#alpha #c #t @(ex_intro … 2) @ex_intro
  [|% [% |cases t normalize // ] ]
qed. 

(***************************** replace a with f a *****************************)

definition writef ≝ λalpha,f.
  mk_TM alpha write_states
  (λp.let 〈q,a〉 ≝ p in
    match pi1 … q with 
    [ O ⇒ 〈wr1,Some ? (f a),N〉
    | S _ ⇒ 〈wr1,None ?,N〉 ])
  wr0 (λx.x == wr1).

definition R_writef ≝ λalpha,f,t1,t2.
  ∀c. current ? t1 = c  →
  t2 = midtape alpha (left ? t1) (f c) (right ? t1).
  
lemma sem_writef : ∀alpha,f.
  writef alpha f  ⊨ R_writef alpha f.
#alpha #f #t @(ex_intro … 2) @ex_intro
  [|% [% |cases t normalize // ] ]
qed. 

(******************** moves the head one step to the right ********************)

definition move_states ≝ initN 2.
definition move0 : move_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition move1 : move_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition move_r ≝ 
  λalpha:FinSet.mk_TM alpha move_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈move1,None ?,N〉
    | Some a' ⇒ match (pi1 … q) with
      [ O ⇒ 〈move1,Some ? a',R〉
      | S q ⇒ 〈move1,None ?,N〉 ] ])
  move0 (λq.q == move1).
  
definition R_move_r ≝ λalpha,t1,t2.
  (current ? t1 = None ? → t1 = t2) ∧  
  ∀ls,c,rs.
    t1 = midtape alpha ls c rs → 
    t2 = mk_tape ? (c::ls) (option_hd ? rs) (tail ? rs).
(*
  (current ? t1 = None ? ∧ t1 = t2) ∨ 
  ∃ls,c,rs.
  t1 = midtape alpha ls c rs ∧ 
  t2 = mk_tape ? (c::ls) (option_hd ? rs) (tail ? rs).*)
    
lemma sem_move_r :
  ∀alpha.Realize ? (move_r alpha) (R_move_r alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | % // #ls #c #rs #H destruct ] ]
|#a #al @ex_intro
  [| % [ % | % // #ls #c #rs #H destruct ] ]
|#a #al @ex_intro
  [| % [ % | % // #ls #c #rs #H destruct ] ]
| #ls #c #rs
  @ex_intro [| % [ % | % [whd in ⊢ ((??%?)→?); #H destruct]
  #ls1 #c1 #rs1 #H destruct cases rs1 // ] ] ]
qed.

(******************** moves the head one step to the left *********************)

definition move_l ≝ 
  λalpha:FinSet.mk_TM alpha move_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈move1,None ?,N〉
    | Some a' ⇒ match pi1 … q with
      [ O ⇒ 〈move1,Some ? a',L〉
      | S q ⇒ 〈move1,None ?,N〉 ] ])
  move0 (λq.q == move1).

definition R_move_l ≝ λalpha,t1,t2.
  (current ? t1 = None ? → t1 = t2) ∧  
  ∀ls,c,rs.
    t1 = midtape alpha ls c rs → 
    t2 = mk_tape ? (tail ? ls) (option_hd ? ls) (c::rs).
    
lemma sem_move_l :
  ∀alpha.Realize ? (move_l alpha) (R_move_l alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | % // #ls #c #rs #H destruct ] ]
|#a #al @ex_intro
  [| % [ % | % // #ls #c #rs #H destruct ] ]
|#a #al @ex_intro
  [| % [ % | % // #ls #c #rs #H destruct ] ]
| #ls #c #rs
  @ex_intro [| % [ % | % [whd in ⊢ ((??%?)→?); #H destruct]
  #ls1 #c1 #rs1 #H destruct cases ls1 // ] ] ]
qed.

(* a slightly different move machine. *)
definition smove_states ≝ initN 2.

definition smove0 : smove_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition smove1 : smove_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition trans_smove ≝ 
 λsig,D.
 λp:smove_states × (option sig).
 let 〈q,a〉 ≝ p in match (pi1 … q) with
 [ O ⇒ 〈smove1,None sig, D〉
 | S _ ⇒ 〈smove1,None sig, N〉 ].

definition move ≝ 
  λsig,D.mk_TM sig smove_states (trans_smove sig D) smove0 (λq.q == smove1).

definition Rmove ≝ 
  λalpha,D,t1,t2. t2 = tape_move alpha t1 D.

lemma sem_move_single :
  ∀alpha,D.move alpha D ⊨ Rmove alpha D.
#alpha #D #int %{2} %{(mk_config ? smove_states smove1 ?)} [| % % ]
qed.

(********************************* test char **********************************)

(* the test_char machine ends up in two different states q1 and q2 wether or not
the current character satisfies a boolean test function passed as a parameter to
the machine.
The machine ends up in q1 also in case there is no current character.
*)

definition tc_states ≝ initN 3.

definition tc_start : tc_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition tc_true : tc_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition tc_false : tc_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition test_char ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha tc_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈tc_false, None ?,N〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈tc_true,None ?,N〉
     | false ⇒ 〈tc_false,None ?,N〉 ]])
  tc_start (λx.notb (x == tc_start)).

definition Rtc_true ≝ 
  λalpha,test,t1,t2.
   (∃c. current alpha t1 = Some ? c ∧ test c = true) ∧ t2 = t1.
   
definition Rtc_false ≝ 
  λalpha,test,t1,t2.
    (∀c. current alpha t1 = Some ? c → test c = false) ∧ t2 = t1.
     
lemma tc_q0_q1 :
  ∀alpha,test,ls,a0,rs. test a0 = true → 
  step alpha (test_char alpha test)
    (mk_config ?? tc_start (midtape … ls a0 rs)) =
  mk_config alpha (states ? (test_char alpha test)) tc_true
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?); 
whd in match (trans … 〈?,?〉); >Htest %
qed.
     
lemma tc_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (test_char alpha test)
    (mk_config ?? tc_start (midtape … ls a0 rs)) =
  mk_config alpha (states ? (test_char alpha test)) tc_false
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?); 
whd in match (trans … 〈?,?〉); >Htest %
qed.

lemma sem_test_char :
  ∀alpha,test.
  accRealize alpha (test_char alpha test) 
    tc_true (Rtc_true alpha test) (Rtc_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? tc_false (niltape ?))) %
  [ % // normalize #Hfalse destruct | #_ normalize % // #c #Hfalse destruct (Hfalse) ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? tc_false (leftof ? a al)))
  % [ % // normalize #Hfalse destruct | #_ normalize % // #c #Hfalse destruct (Hfalse) ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? tc_false (rightof ? a al)))
  % [ % // normalize #Hfalse destruct | #_ normalize % // #c #Hfalse destruct (Hfalse) ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? tc_true ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >tc_q0_q1 //
        | #_ % // @(ex_intro … c) /2/]
      | * #Hfalse @False_ind @Hfalse % ]
    ]
  | @(ex_intro ?? (mk_config ?? tc_false (midtape ? ls c rs)))
    % 
    [ %
      [ whd in ⊢ (??%?); >tc_q0_q2 //
      | whd in ⊢ ((??%%)→?); #Hfalse destruct (Hfalse) ]
    | #_ % // #c0 whd in ⊢ ((??%?)→?); #Hc0 destruct (Hc0) //
    ]
  ]
]
qed.

lemma test_char_inv : 
  ∀sig.∀P:tape sig → Prop.∀f,t,t0.P t → Rtc_true sig f t t0 → P t0.
#sig #P #f #t #t0 #HPt * #_ //
qed.

definition test_null ≝ λalpha.test_char alpha (λ_.true).

definition R_test_null_true ≝ λalpha,t1,t2.
  current alpha t1 ≠ None ? ∧ t1 = t2.
  
definition R_test_null_false ≝ λalpha,t1,t2.
  current alpha t1 = None ? ∧ t1 = t2.
  
lemma sem_test_null : ∀alpha.
  test_null alpha ⊨ [ tc_true : R_test_null_true alpha, R_test_null_false alpha].
#alpha #t1 cases (sem_test_char alpha (λ_.true) t1) #k * #outc * * #Hloop #Htrue
#Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Houtc cases (Htrue ?) [| @Houtc] * #c * #Hcurt1 #_ #Houtc1 %
  [ >Hcurt1 % #H destruct (H) | <Houtc1 % ] ]
| #Houtc cases (Hfalse ?) [| @Houtc] #Habsurd #Houtc %
  [ cases (current alpha t1) in Habsurd; // #c1 #Habsurd 
    lapply (Habsurd ? (refl ??)) #H destruct (H)
  | <Houtc % ] ]
qed.

(************************************* swap ***********************************)
definition swap_states : FinSet → FinSet ≝ 
  λalpha:FinSet.FinProd (initN 4) alpha.

definition swap0 : initN 4 ≝ mk_Sig ?? 0 (leb_true_to_le 1 4 (refl …)).
definition swap1 : initN 4 ≝ mk_Sig ?? 1 (leb_true_to_le 2 4 (refl …)).
definition swap2 : initN 4 ≝ mk_Sig ?? 2 (leb_true_to_le 3 4 (refl …)).
definition swap3 : initN 4 ≝ mk_Sig ?? 3 (leb_true_to_le 4 4 (refl …)).

definition swap_r ≝ 
 λalpha:FinSet.λfoo:alpha.
 mk_TM alpha (swap_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<4) q' in
  match a with 
  [ None ⇒ 〈〈swap3,foo〉,None ?,N〉 (* if tape is empty then stop *)
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* q0 *) 〈〈swap1,a'〉,Some ? a',R〉  (* save in register and move R *)
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *) 〈〈swap2,a'〉,Some ? b,L〉 (* swap with register and move L *)
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *) 〈〈swap3,foo〉,Some ? b,N〉 (* copy from register and stay *)
      | S q' ⇒ (* q3 *) 〈〈swap3,foo〉,None ?,N〉 (* final state *)
      ]
    ]
  ]])
  〈swap0,foo〉
  (λq.\fst q == swap3).
  
definition Rswap_r ≝ 
  λalpha,t1,t2.
    (∀b,ls.
      t1 = midtape alpha ls b [ ] → 
      t2 = rightof ? b ls) ∧
    (∀a,b,ls,rs. 
      t1 = midtape alpha ls b (a::rs) → 
      t2 = midtape alpha ls a (b::rs)).

lemma sem_swap_r : ∀alpha,foo.
  swap_r alpha foo ⊨ Rswap_r alpha. 
#alpha #foo *
  [@(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈swap3,foo〉 (niltape ?)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct]
  |#l0 #lt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈swap3,foo〉 (leftof ? l0 lt0)))
   % [% | % [#b #ls | #a #b #ls #rs] #H destruct]
  |#r0 #rt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈swap3,foo〉 (rightof ? r0 rt0)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct] 
  | #lt #c #rt @(ex_intro ?? 4) cases rt
    [@ex_intro [|% [ % | %
      [#b #ls #H destruct normalize // |#a #b #ls #rs #H destruct]]]
    |#r0 #rt0 @ex_intro [| % [ % | %
      [#b #ls #H destruct | #a #b #ls #rs #H destruct normalize //
    ]
  ]
qed.

definition swap_l ≝ 
 λalpha:FinSet.λfoo:alpha.
 mk_TM alpha (swap_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<4) q' in
  match a with 
  [ None ⇒ 〈〈swap3,foo〉,None ?,N〉 (* if tape is empty then stop *)
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* q0 *) 〈〈swap1,a'〉,Some ? a',L〉  (* save in register and move L *)
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *) 〈〈swap2,a'〉,Some ? b,R〉 (* swap with register and move R *)
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *) 〈〈swap3,foo〉,Some ? b,N〉 (* copy from register and stay *)
      | S q' ⇒ (* q3 *) 〈〈swap3,foo〉,None ?,N〉 (* final state *)
      ]
    ]
  ]])
  〈swap0,foo〉
  (λq.\fst q == swap3).

definition Rswap_l ≝ 
  λalpha,t1,t2.
   (∀b,rs.  
     t1 = midtape alpha [ ] b rs → 
     t2 = leftof ? b rs) ∧
   (∀a,b,ls,rs.  
      t1 = midtape alpha (a::ls) b rs → 
      t2 = midtape alpha (b::ls) a rs).

lemma sem_swap_l : ∀alpha,foo.
  swap_l alpha foo ⊨ Rswap_l alpha. 
#alpha #foo *
  [@(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈swap3,foo〉 (niltape ?)))
   % [% |% [#b #rs | #a #b #ls #rs] #H destruct]
  |#l0 #lt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈swap3,foo〉 (leftof ? l0 lt0)))
   % [% | % [#b #rs | #a #b #ls #rs] #H destruct]
  |#r0 #rt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈swap3,foo〉 (rightof ? r0 rt0)))
   % [% |% [#b #rs | #a #b #ls #rs] #H destruct] 
  | #lt #c #rt @(ex_intro ?? 4) cases lt
    [@ex_intro [|% [ % | %
      [#b #rs #H destruct normalize // |#a #b #ls #rs #H destruct]]]
    |#r0 #rt0 @ex_intro [| % [ % | %
      [#b #rs #H destruct | #a #b #ls #rs #H destruct normalize //
    ]
  ]
qed.

(********************************** combine ***********************************)
(* replace the content x of a cell with a combiation f(x,y) of x and the content
y of the adiacent cell *)

definition combf_states : FinSet → FinSet ≝ 
  λalpha:FinSet.FinProd (initN 4) alpha.

definition combf0 : initN 4 ≝ mk_Sig ?? 0 (leb_true_to_le 1 4 (refl …)).
definition combf1 : initN 4 ≝ mk_Sig ?? 1 (leb_true_to_le 2 4 (refl …)).
definition combf2 : initN 4 ≝ mk_Sig ?? 2 (leb_true_to_le 3 4 (refl …)).
definition combf3 : initN 4 ≝ mk_Sig ?? 3 (leb_true_to_le 4 4 (refl …)).

definition combf_r ≝ 
 λalpha:FinSet.λf.λfoo:alpha.
 mk_TM alpha (combf_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<4) q' in
  match a with 
  [ None ⇒ 〈〈combf3,foo〉,None ?,N〉 (* if tape is empty then stop *)
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* q0 *) 〈〈combf1,a'〉,Some ? a',R〉  (* save in register and move R *)
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *) 〈〈combf2,f b a'〉,Some ? a',L〉 
      (* combine in register and move L *)
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *) 〈〈combf3,foo〉,Some ? b,R〉 
        (* copy from register and move R *)
      | S q' ⇒ (* q3 *) 〈〈combf3,foo〉,None ?,N〉 (* final state *)
      ]
    ]
  ]])
  〈combf0,foo〉
  (λq.\fst q == combf3).
  
definition Rcombf_r ≝ 
  λalpha,f,t1,t2.
    (∀b,ls.
      t1 = midtape alpha ls b [ ] → 
      t2 = rightof ? b ls) ∧
    (∀a,b,ls,rs. 
      t1 = midtape alpha ls b (a::rs) → 
      t2 = midtape alpha ((f b a)::ls) a rs).

lemma sem_combf_r : ∀alpha,f,foo.
  combf_r alpha f foo ⊨ Rcombf_r alpha f. 
#alpha #f #foo *
  [@(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (niltape ?)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct]
  |#l0 #lt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (leftof ? l0 lt0)))
   % [% | % [#b #ls | #a #b #ls #rs] #H destruct]
  |#r0 #rt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (rightof ? r0 rt0)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct] 
  | #lt #c #rt @(ex_intro ?? 4) cases rt
    [@ex_intro [|% [ % | %
      [#b #ls #H destruct normalize // |#a #b #ls #rs #H destruct]]]
    |#r0 #rt0 @ex_intro [| % [ % | %
      [#b #ls #H destruct | #a #b #ls #rs #H destruct normalize //
    ]
  ]
qed.

definition combf_l ≝ 
 λalpha:FinSet.λf.λfoo:alpha.
 mk_TM alpha (combf_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<4) q' in
  match a with 
  [ None ⇒ 〈〈combf3,foo〉,None ?,N〉 (* if tape is empty then stop *)
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* q0 *) 〈〈combf1,a'〉,Some ? a',L〉  (* save in register and move R *)
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *) 〈〈combf2,f b a'〉,Some ? a',R〉 
      (* combine in register and move L *)
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *) 〈〈combf3,foo〉,Some ? b,L〉 
        (* copy from register and move R *)
      | S q' ⇒ (* q3 *) 〈〈combf3,foo〉,None ?,N〉 (* final state *)
      ]
    ]
  ]])
  〈combf0,foo〉
  (λq.\fst q == combf3).
  
definition Rcombf_l ≝ 
  λalpha,f,t1,t2.
    (∀b,rs.
      t1 = midtape alpha [ ] b rs → 
      t2 = leftof ? b rs) ∧
    (∀a,b,ls,rs. 
      t1 = midtape alpha (a::ls) b rs → 
      t2 = midtape alpha ls a ((f b a)::rs)).

lemma sem_combf_l : ∀alpha,f,foo.
  combf_l alpha f foo ⊨ Rcombf_l alpha f. 
#alpha #f #foo *
  [@(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (niltape ?)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct]
  |#l0 #lt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (leftof ? l0 lt0)))
   % [% | % [#b #ls | #a #b #ls #rs] #H destruct]
  |#r0 #rt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (rightof ? r0 rt0)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct] 
  | #lt #c #rt @(ex_intro ?? 4) cases lt
    [@ex_intro [|% [ % | %
      [#b #ls #H destruct normalize // |#a #b #ls #rs #H destruct]]]
    |#r0 #rt0 @ex_intro [| % [ % | %
      [#b #ls #H destruct | #a #b #ls #rs #H destruct normalize //
    ]
  ]
qed.

(********************************* new_combine ********************************)
(* replace the content x of a cell with a combiation f(x,y) of x and the content
y of the adiacent cell; if there is no adjacent cell, combines with a default 
value foo *)

definition ncombf_r ≝ 
 λalpha:FinSet.λf.λfoo:alpha.
 mk_TM alpha (combf_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<4) q' in
  match a with 
  [ None ⇒ if (eqb q' 1)then (* if on right cell, combine in register and move L *) 
           〈〈combf2,f b foo〉,None ?,L〉
           else 〈〈combf3,foo〉,None ?,N〉 (* else stop *)
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* q0 *) 〈〈combf1,a'〉,Some ? a',R〉  (* save in register and move R *)
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *) 〈〈combf2,f b a'〉,Some ? a',L〉 
      (* combine in register and move L *)
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *) 〈〈combf3,foo〉,Some ? b,R〉 
        (* copy from register and move R *)
      | S q' ⇒ (* q3 *) 〈〈combf3,foo〉,None ?,N〉 (* final state *)
      ]
    ]
  ]])
  〈combf0,foo〉
  (λq.\fst q == combf3).
  
definition Rncombf_r ≝ 
  λalpha,f,foo,t1,t2.
    (∀b,ls.
      t1 = midtape alpha ls b [ ] → 
      t2 = rightof ? (f b foo) ls) ∧
    (∀a,b,ls,rs. 
      t1 = midtape alpha ls b (a::rs) → 
      t2 = midtape alpha ((f b a)::ls) a rs).

lemma sem_ncombf_r : ∀alpha,f,foo.
  ncombf_r alpha f foo ⊨ Rncombf_r alpha f foo. 
#alpha #f #foo *
  [@(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (niltape ?)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct]
  |#l0 #lt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (leftof ? l0 lt0)))
   % [% | % [#b #ls | #a #b #ls #rs] #H destruct]
  |#r0 #rt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (rightof ? r0 rt0)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct] 
  | #lt #c #rt @(ex_intro ?? 4) cases rt
    [@ex_intro [|% [ % | %
      [#b #ls #H destruct normalize // |#a #b #ls #rs #H destruct]]]
    |#r0 #rt0 @ex_intro [| % [ % | %
      [#b #ls #H destruct | #a #b #ls #rs #H destruct normalize //
    ]
  ]
qed.

definition ncombf_l ≝ 
 λalpha:FinSet.λf.λfoo:alpha.
 mk_TM alpha (combf_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<4) q' in
  match a with 
  [ None ⇒ if (eqb q' 1)then 
           (* if on left cell, combine in register and move R *) 
           〈〈combf2,f b foo〉,None ?,R〉
           else 〈〈combf3,foo〉,None ?,N〉 (* else stop *)
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* q0 *) 〈〈combf1,a'〉,Some ? a',L〉  (* save in register and move R *)
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *) 〈〈combf2,f b a'〉,Some ? a',R〉 
      (* combine in register and move L *)
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *) 〈〈combf3,foo〉,Some ? b,L〉 
        (* copy from register and move R *)
      | S q' ⇒ (* q3 *) 〈〈combf3,foo〉,None ?,N〉 (* final state *)
      ]
    ]
  ]])
  〈combf0,foo〉
  (λq.\fst q == combf3).
  
definition Rncombf_l ≝ 
  λalpha,f,foo,t1,t2.
    (∀b,rs.
      t1 = midtape alpha [ ] b rs → 
      t2 = leftof ? (f b foo) rs) ∧
    (∀a,b,ls,rs. 
      t1 = midtape alpha (a::ls) b rs → 
      t2 = midtape alpha ls a ((f b a)::rs)).

lemma sem_ncombf_l : ∀alpha,f,foo.
  ncombf_l alpha f foo ⊨ Rncombf_l alpha f foo. 
#alpha #f #foo *
  [@(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (niltape ?)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct]
  |#l0 #lt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (leftof ? l0 lt0)))
   % [% | % [#b #ls | #a #b #ls #rs] #H destruct]
  |#r0 #rt0 @(ex_intro ?? 2) @(ex_intro … (mk_config ?? 〈combf3,foo〉 (rightof ? r0 rt0)))
   % [% |% [#b #ls | #a #b #ls #rs] #H destruct] 
  | #lt #c #rt @(ex_intro ?? 4) cases lt
    [@ex_intro [|% [ % | %
      [#b #ls #H destruct normalize // |#a #b #ls #rs #H destruct]]]
    |#r0 #rt0 @ex_intro [| % [ % | %
      [#b #ls #H destruct | #a #b #ls #rs #H destruct normalize //
    ]
  ]
qed.
