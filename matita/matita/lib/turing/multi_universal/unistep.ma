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


include "turing/multi_universal/unistep_aux.ma".
include "turing/multi_universal/match.ma".

definition exec_move ≝ 
  cfg_to_obj · tape_move_obj · restart_tape prg 2 · obj_to_cfg.

definition R_exec_move ≝ λt1,t2:Vector (tape FSUnialpha) 3.
∀c,m,ls1,ls2,rs2.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls1@[bar]) (None ?) [ ] → 
  nth prg ? t1 (niltape ?) = midtape FSUnialpha (ls2@[bar]) m rs2 →
  only_bits (list_of_tape ? (nth obj ? t1 (niltape ?))) →
  c ≠ bar → m ≠ bar →
  let new_obj ≝ 
      tape_move_mono ? (nth obj ? t1 (niltape ?)) 
        〈char_to_bit_option c, char_to_move m〉 in
  let next_c ≝ low_char' (current ? new_obj) in 
  let new_cfg ≝ midtape ? [ ] bar ((reverse ? ls1)@[next_c]) in 
  let new_prg ≝ midtape FSUnialpha [ ] bar ((reverse ? ls2)@m::rs2) in
  t2 = Vector_of_list ? [new_obj;new_cfg;new_prg].


lemma sem_exec_move: exec_move ⊨ R_exec_move.
@(sem_seq_app ??????? sem_cfg_to_obj1
  (sem_seq ?????? sem_tape_move_obj
   (sem_seq ?????? (sem_restart_tape ???) sem_obj_to_cfg1))) //
#ta #tout * #t1 * #semM1 * #t2 * #semM2 * #t3 * #semM3 #semM4 
#c #m #ls1 #ls2 #rs2 #Hcfg #Hprg #Honlybits #Hc #Hm 
(* M1 = cfg_to_obj *)
lapply (semM1 … Hcfg Hc) #Ht1 
(* M2 = tape_move *)
whd in semM2; >Ht1 in semM2; -Ht1
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
>Hprg #Ht2 lapply (Ht2 … (refl ??)) -Ht2
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec // >change_vec_commute [2:@eqb_false_to_not_eq %]
>change_vec_change_vec #Ht2 
(* M3 = restart prg *) 
whd in semM3; >Ht2 in semM3; #semM3 lapply (semM3 … (refl ??)); -semM3
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
>nth_change_vec_neq [2:@eqb_false_to_not_eq %] #Ht3
(* M4 = obj_to_cfg *) 
whd in semM4; >Ht3 in semM4; 
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec [2:@leb_true_to_le %] #semM4 lapply (semM4 … (refl ??)) -semM4
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec [2:@leb_true_to_le %] #semM4 >(semM4 ?)
  [(* tape by tape *)
   @(eq_vec … (niltape ?)) #i #lei2 
   cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
    [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
      [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec [2:@leb_true_to_le %] %
      |#Hi >Hi (* obj tape *)
       >nth_change_vec [2:@leb_true_to_le %] whd in ⊢ (???%);
       >reverse_cons >reverse_append >reverse_single 
       whd in match (option_hd ??); whd in match (tail ??);
       whd in ⊢ (??%?); %
      ]
    |#Hi >Hi (* prg tape *)
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec [2:@leb_true_to_le %] whd in ⊢ (???%);
     >Hprg whd in match (list_of_tape ??); >reverse_append
     >reverse_single % 
    ]
  |#b #Hcurrent @(list_of_tape_write ? is_bit … (char_to_bit_option c) ? Honlybits)
    [#b0 cases c
      [#b1 whd in ⊢ (??%?→?); #Hbit destruct (Hbit) %
      |whd in ⊢ (??%?→?); #Hbit destruct (Hbit)
      |whd in ⊢ (??%?→?); #Hbit destruct (Hbit)
      ]
    |>(list_of_tape_move … (char_to_move m)) @current_in_list @Hcurrent
    ]
  ]
qed.
       
definition unistep ≝ 
  match_m cfg prg FSUnialpha 2 · 
  restart_tape cfg 2 · mmove cfg ? 2 R · copy prg cfg FSUnialpha 2 ·
  exec_move.

(*
definition legal_tape ≝ λn,l,h,t.
  ∃state,char,table.
  nth cfg ? t1 (niltape ?) = midtape ? [ ] bar (state@[char]) →
  is_config n (bar::state@[char]) →  
  nth prg ? t1 (niltape ?) = midtape ? [ ] bar table →
  bar::table = table_TM n l h → *)
  
definition deterministic_tuples ≝ λn,h,l.
 ∀t1,t2,conf,out1,out2.
  is_config n conf →
  mem ? t1 l → mem ? t2 l →
  tuple_encoding n h t1 = conf@out1 →
    tuple_encoding n h t2 = conf@out2 → out1 = out2.

definition R_unistep ≝ λn,l,h.λt1,t2: Vector ? 3.
  ∀state,char,table.
  (* cfg *)
  nth cfg ? t1 (niltape ?) = midtape ? [ ] bar (state@[char]) →
  is_config n (bar::state@[char]) →  
  (* prg *)
  nth prg ? t1 (niltape ?) = midtape ? [ ] bar table →
  bar::table = table_TM n l h →
  (* obj *)
  only_bits (list_of_tape ? (nth obj ? t1 (niltape ?))) →
  (* deterministic tuples *)
  deterministic_tuples n h l →
  let conf ≝ (bar::state@[char]) in
  (∃ll,lr.bar::table = ll@conf@lr) →
(*
    ∃nstate,nchar,m,t. tuple_encoding n h t = (conf@nstate@[nchar;m]) ∧ 
    mem ? t l ∧  *)
    ∀nstate,nchar,m,t. 
    tuple_encoding n h t = (conf@nstate@[nchar;m])→ 
    mem ? t l →
    let new_obj ≝ 
     tape_move_mono ? (nth obj ? t1 (niltape ?)) 
       〈char_to_bit_option nchar,char_to_move m〉 in
    let next_char ≝ low_char' (current ? new_obj) in
    t2 = 
      change_vec ??
        (change_vec ?? t1 (midtape ? [ ] bar (nstate@[next_char])) cfg)
        new_obj obj.
        
lemma lt_obj : obj < 3. // qed.
lemma lt_cfg : cfg < 3. // qed.
lemma lt_prg : prg < 3. // qed.

definition R_copy_strict ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ((current ? (nth src ? int (niltape ?)) = None ? ∨
    current ? (nth dst ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,x0,rs,ls0,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x rs →
    nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    |rs0| ≤ |rs| → 
    (∃rs1,rs2.rs = rs1@rs2 ∧ |rs1| = |rs0| ∧
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs1@x::ls) (option_hd sig rs2)
            (tail sig rs2)) src)
            (mk_tape sig (reverse sig rs1@x::ls0) (None sig) []) dst)).

lemma sem_copy_strict : ∀src,dst,sig,n. src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n ⊨ R_copy_strict src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst @(Realize_to_Realize … (sem_copy …)) //
#ta #tb * #Htb1 #Htb2 % [ @Htb1 ]
#ls #x #x0 #rs #ls0 #rs0 #Htamid_src #Htamid_dst #Hlen
cases (Htb2 … Htamid_src Htamid_dst) -Htb1 -Htb2
[ * #rs1 * #rs2 * * #Hrs0 #Heq #Htb <Heq in Hlen; >Hrs0 >length_append
  >(plus_n_O (|rs1|)) #Hlen cut (|rs2| ≤ 0) [ /2 by le_plus_to_le/ ]
  #Hlenrs2 cut (rs2 = [ ]) 
  [ cases rs2 in Hlenrs2; // #r3 #rs3 normalize #H @False_ind cases (not_le_Sn_O (|rs3|)) /2/ ]
  #Hrs2 destruct (Hrs2) >append_nil in Hrs0; #Hrs0 destruct (Hrs0) -Hlenrs2 -Hlen
  <plus_n_O <plus_n_O %{rs} %{[ ]} >append_nil % [ % // ] @Htb
| * #rs1 * #rs2 #H %{rs1} %{rs2} @H ]
qed.

lemma config_to_len : ∀n,b,q,c.is_config n (b::q@[c]) → |q| = S n.
#n #b #q #c * #q0 * #cin * * * #_ #_ #Hq0 #H >(?:q = q0) //
lapply (cons_injective_r ????? H) #H1 @(append_l1_injective … H1)
lapply (eq_f … (length ?) … H) normalize >length_append >length_append
<plus_n_Sm <plus_n_Sm <plus_n_O <plus_n_O #Hlen destruct (Hlen) //
qed.

lemma sem_unistep_low : ∀n,l,h.unistep ⊨ R_unistep n l h.
#n #l #h
@(sem_seq_app ??????? (sem_match_m cfg prg FSUnialpha 2 ???)
  (sem_seq ?????? (sem_restart_tape ???)
   (sem_seq ?????? (sem_move_multi ? 2 cfg R ?)
    (sem_seq ?????? (sem_copy_strict prg cfg FSUnialpha 2 ???)
     (sem_exec_move …)))))
  /2 by le_n,sym_not_eq/
#ta #tb #HR #state #char #table #Hta_cfg #Hcfg #Hta_prg #Htable
#Hbits_obj #Hdeterm #Hmatching
#nstate #nchar #m #t #Htuple #Hmatch
cases HR -HR #tc * whd in ⊢ (%→?); 
>Hta_cfg #H cases (H ?? (refl ??)) -H 
(* prg starts with a bar, so it's not empty *) #_
>Hta_prg #H lapply (H ??? (refl ??)) -H *
[| cases Hmatching #ll * #lr #H >H 
   #Hfalse @False_ind cases (Hfalse ll lr) #H1 @H1 //]
* #ll * #lr * #Hintable  #Htc
* #td * whd in ⊢ (%→?); >Htc
>nth_change_vec_neq [|@sym_not_eq //] >(nth_change_vec ?????? lt_cfg)
#Htd lapply (Htd ? (refl ??)) -Htd
>change_vec_commute [|@sym_not_eq //] >change_vec_change_vec
>(?: list_of_tape ? (mk_tape ? (reverse ? (state@[char])@[bar]) (None ?) [ ]) =
     bar::state@[char]) 
[|whd in ⊢ (??%?); >left_mk_tape >reverse_append >reverse_reverse
  >current_mk_tape >right_mk_tape [| #_ %2 % ] normalize >append_nil % ]
whd in ⊢ (???(???(????%?)??)→?); whd in match (tail ??); #Htd
(* move cfg to R *)
* #te * whd in ⊢ (%→?); >Htd
>change_vec_commute [|@sym_not_eq //] >change_vec_change_vec
>nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec [2:@leb_true_to_le %]
cut (∃ll1.ll@[bar] = bar::ll1) 
[ cases ll in Hintable; [ #_ %{[ ]} % ] 
  #llhd #lltl normalize #H destruct (H) %{(lltl@[bar])} % ] * #ll1 #Hll1
>Htable in Hintable; #Hintable #Hte
(* copy *)
lapply (table_to_list ???? Hcfg ?? Hintable) * #out * #lr0 * #t0
* * #Hlr #Htuple_t0 #mem_t0 
cut (out = nstate@[nchar;m])
  [@(Hdeterm … Hcfg mem_t0 Hmatch Htuple_t0 Htuple)] #Hout
>(append_cons ? nchar) in Htuple; #Htuple
lapply (tuple_to_config ?????? Hcfg … Htuple) #newconfig
cut (∃fo,so.state = fo::so ∧ |so| = n)
[ lapply (config_to_len … Hcfg) cases state [ normalize #H destruct (H) ]
  #fo #so normalize #H destruct (H) %{fo} %{so} % // ]
* #fo * #so * #Hstate_exp #Hsolen
cut (∃fn,sn.nstate = fn::sn  ∧ |sn| = n)
[ lapply (config_to_len … newconfig) cases nstate [ normalize #H destruct (H) ]
  #fn #sn normalize #H destruct (H) %{fn} %{sn} % // ]
* #fn * #sn * #Hnewstate_exp #Hsnlen
>Hstate_exp >Hout in Hlr; >Hnewstate_exp whd in ⊢ (???%→?); #Hlr
* #tf * * #_ >Hte >(nth_change_vec ?????? lt_prg)
>nth_change_vec_neq [|@sym_not_eq //] >(nth_change_vec ?????? lt_cfg)
>Hstate_exp >Hnewstate_exp >Hlr
whd in match (mk_tape ????); whd in match (tape_move ???);
#Htf cases (Htf ?????? (refl ??) (refl ??) ?) -Htf
[| whd in match (tail ??); >length_append >length_append 
   >Hsolen >length_append >Hsnlen normalize //]
#rs1 * #rs2 whd in match (tail ??); * *
#Hrs1rs2 #Hrs1len
>change_vec_change_vec >change_vec_commute [|@sym_not_eq //]
>change_vec_change_vec >append_nil #Htf 
(* exec_move *)
>append_cons in Hrs1rs2; >associative_append #Hrs1rs2
cut ((sn@[nchar])=rs1)
  [@(append_l1_injective ?????? Hrs1rs2) >Hrs1len 
   >length_append >length_append normalize >Hsolen >Hsnlen % ] #Hrs1  
cut (m::lr0=rs2) [@(append_l2_injective ?????? Hrs1rs2) >Hrs1 % ] #Hrs2 
whd in ⊢ (%→?); >Htf >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec [2:@leb_true_to_le %] 
>nth_change_vec [2:@leb_true_to_le %]
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>nth_change_vec_neq [2:@eqb_false_to_not_eq %]
>append_cons <Hrs1 >reverse_append >reverse_single 
<Hrs2 >(append_cons … bar ll) >Hll1 >reverse_cons
#sem_exec_move 
lapply
  (sem_exec_move ? m ?
    (([nchar]@reverse FSUnialpha sn)
          @fn::reverse FSUnialpha (ll1@(fo::so)@[char])) lr0 … (refl ??) ????) 
  [ cut (tuple_TM (S n) (tuple_encoding n h t)) // >Htuple
    * #qin * #cin * #qout * #cout * #mv * * * * #_ #Hmv #_ #_
    normalize >(?: bar::qin@cin::qout@[cout;mv] = (bar::qin@cin::qout@[cout])@[mv])
    [| normalize >associative_append normalize >associative_append % ] 
    >(?: bar::(state@[char])@(nstate@[nchar])@[m] = (bar::(state@[char])@(nstate@[nchar]))@[m]) 
    [|normalize >associative_append >associative_append >associative_append >associative_append >associative_append % ] 
    #Heq lapply (append_l2_injective_r ?????? Heq) // #H destruct (H) //
  | cases newconfig #qout * #cout * * * #_ #Hcout #_ #H destruct (H) -H
    lapply (append_l2_injective_r ?????? e0) // #H destruct (H) @Hcout 
  |@Hbits_obj
  |whd in ⊢ (??%?); >associative_append >associative_append 
   >associative_append  %
  |#Htb >Htb @(eq_vec … (niltape ?)) (* tape by tape *) #i #lei2 
   cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
    [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
      [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
       (* obj tape *)
       >nth_change_vec [2:@leb_true_to_le %] % 
      |(* cfg tape *) #eqi >eqi
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
       >nth_change_vec [2:@leb_true_to_le %]  
       whd in ⊢ (??%?); cut (∀A.∀l:list A.[]@l = l) [//] #Hnil >Hnil
       >reverse_append >reverse_single >reverse_reverse %
       (* idem *)
      ]
    |(* prg tape *) #eqi >eqi
      >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
      >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
      >Hta_prg whd in ⊢ (??%?); @eq_f @(cons_injective_r ? bar bar)
      >Htable >Hintable >reverse_append >reverse_cons
      >reverse_reverse >reverse_cons >reverse_reverse
      >associative_append >associative_append >associative_append
      >(append_cons ? bar ll) >Hll1 @eq_f @eq_f <Hstate_exp @eq_f
      >Hnewstate_exp >Hlr normalize >associative_append >associative_append %
    ]
  ]
qed.

definition tape_map ≝ λA,B:FinSet.λf:A→B.λt.
  mk_tape B (map ?? f (left ? t)) 
    (option_map ?? f (current ? t)) 
    (map ?? f (right ? t)).

(* da spostare *)
lemma map_reverse: ∀A,B,f,l. 
  map ?? f (reverse A l) = reverse B (map ?? f l).
#A #B #f #l elim l //
#a #l1 #Hind >reverse_cons >reverse_cons <map_append @eq_f2 //
qed.

lemma map_list_of_tape: ∀A,B,f,t.
  list_of_tape B (tape_map ?? f t) = map ?? f (list_of_tape A t).
#A #B #f * // 
  [#a #l normalize >rev_append_def >rev_append_def >append_nil
   >append_nil <map_append <map_reverse @eq_f2 //
  |#rs #a #ls normalize >rev_append_def >rev_append_def
   >append_nil >append_nil <map_append normalize 
   @eq_f2 //
  ]
qed.

lemma low_char_current : ∀t.
  low_char' (current FSUnialpha (tape_map FinBool FSUnialpha bit t))
  = low_char (current FinBool t).
* // qed.

definition low_tapes: ∀M:normalTM.∀c:nconfig (no_states M).Vector ? 3 ≝ 
λM:normalTM.λc:nconfig (no_states M).Vector_of_list ?
  [tape_map ?? bit (ctape ?? c);
   midtape ? [ ] bar 
    ((bits_of_state ? (nhalt M) (cstate ?? c))@[low_char (current ? (ctape ?? c))]);
   midtape ? [ ] bar (tail ? (table_TM ? (graph_enum ?? (ntrans M)) (nhalt M)))
  ].

lemma obj_low_tapes: ∀M,c.
  nth obj ? (low_tapes M c) (niltape ?) = tape_map ?? bit (ctape ?? c).
// qed.

lemma cfg_low_tapes: ∀M,c.
  nth cfg ? (low_tapes M c) (niltape ?) = 
  midtape ? [ ] bar 
    ((bits_of_state ? (nhalt M) (cstate ?? c))@[low_char (current ? (ctape ?? c))]).
// qed.

lemma prg_low_tapes: ∀M,c.
  nth prg ? (low_tapes M c) (niltape ?) = 
  midtape ? [ ] bar (tail ? (table_TM ? (graph_enum ?? (ntrans M)) (nhalt M))).
// qed.

(* commutation lemma for write *)
lemma map_write: ∀t,cout.
 tape_write ? (tape_map FinBool ? bit t) (char_to_bit_option (low_char cout))
  = tape_map ?? bit (tape_write ? t cout).
#t * // #b whd in match (char_to_bit_option ?);
whd in ⊢ (??%%); @eq_f3 [elim t // | // | elim t //]
qed.

(* commutation lemma for moves *)
lemma map_move: ∀t,m.
 tape_move ? (tape_map FinBool ? bit t) (char_to_move (low_mv m))
  = tape_map ?? bit (tape_move ? t m).
#t * // whd in match (char_to_move ?);
  [cases t // * // | cases t // #ls #a * //]
qed.
  
(* commutation lemma for actions *)
lemma map_action: ∀t,cout,m.
 tape_move ? (tape_write ? (tape_map FinBool ? bit t)
    (char_to_bit_option (low_char cout))) (char_to_move (low_mv m)) 
 = tape_map ?? bit (tape_move ? (tape_write ? t cout) m).
#t #cout #m >map_write >map_move % 
qed. 

lemma map_move_mono: ∀t,cout,m.
 tape_move_mono ? (tape_map FinBool ? bit t)
  〈char_to_bit_option (low_char cout), char_to_move (low_mv m)〉
 = tape_map ?? bit (tape_move_mono ? t 〈cout,m〉).
@map_action
qed. 

definition R_unistep_high ≝ λM:normalTM.λt1,t2.
∀c:nconfig (no_states M).
  t1 = low_tapes M c → 
  t2 = low_tapes M (step ? M c). 

lemma R_unistep_equiv : ∀M,t1,t2. 
  R_unistep (no_states M) (graph_enum ?? (ntrans M)) (nhalt M) t1 t2 →
  R_unistep_high M t1 t2.
#M #t1 #t2 #H whd whd in match (nconfig ?); #c #Ht1
lapply (initial_bar ? (nhalt M) (graph_enum ?? (ntrans M)) (nTM_nog ?)) #Htable
(* tup = current tuple *)
cut (∃t.t = 〈〈cstate … c,current ? (ctape … c)〉, 
             ntrans M 〈cstate … c,current ? (ctape … c)〉〉) [% //] * #tup #Htup
(* tup is in the graph *)
cut (mem ? tup (graph_enum ?? (ntrans M)))
  [@memb_to_mem >Htup @(graph_enum_complete … (ntrans M)) %] #Hingraph
(* tupe target = 〈qout,cout,m〉 *)
lapply (decomp_target ? (ntrans M 〈cstate … c,current ? (ctape … c)〉))
* #qout * #cout * #m #Htg >Htg in Htup; #Htup
(* new config *)
cut (step FinBool M c = mk_config ?? qout (tape_move ? (tape_write ? (ctape … c) cout) m))
  [>(config_expand … c) whd in ⊢ (??%?); (* >Htg ?? why not?? *)
   cut (trans ? M 〈cstate  … c, current ? (ctape … c)〉 = 〈qout,cout,m〉) [<Htg %] #Heq1 
   >Heq1 %] #Hstep
(* new state *)
cut (cstate ?? (step FinBool M c) = qout) [>Hstep %] #Hnew_state
(* new tape *)
cut (ctape ?? (step FinBool M c) = tape_move ? (tape_write ? (ctape … c) cout) m)
  [>Hstep %] #Hnew_tape
lapply(H (bits_of_state ? (nhalt M) (cstate ?? c)) 
         (low_char (current ? (ctape ?? c)))
         (tail ? (table_TM ? (graph_enum ?? (ntrans M)) (nhalt M)))
         ???????)        
[<Htable
 lapply(list_to_table … (nhalt M) …Hingraph) * #ll * #lr #Htable1 %{ll} 
 %{(((bits_of_state ? (nhalt M) qout)@[low_char cout;low_mv m])@lr)} 
 >Htable1 @eq_f <associative_append @eq_f2 // >Htup
 whd in ⊢ (??%?); @eq_f >associative_append %
|#tx #ty #conf #outx #outy #isconf #memx #memy #tuplex #tupley
 @(deterministic M … (refl ??) memx memy isconf tuplex tupley)
|>Ht1 >obj_low_tapes >map_list_of_tape elim (list_of_tape ??) 
  [#b @False_ind | #b #tl #Hind #a * [#Ha >Ha //| @Hind]]
|@sym_eq @Htable
|>Ht1 %
|%{(bits_of_state ? (nhalt M) (cstate ?? c))} %{(low_char (current ? (ctape ?? c)))}
 % [% [% [// | cases (current ??) normalize [|#b] % #Hd destruct (Hd)]
      |>length_map whd in match (length ??); @eq_f //]
   |//]
|>Ht1 >cfg_low_tapes //] -H #H 
lapply(H (bits_of_state … (nhalt M) qout) (low_char … cout) 
         (low_mv … m) tup ? Hingraph)
  [>Htup whd in ⊢ (??%?); @eq_f >associative_append %] -H
#Ht2 @(eq_vec ? 3 ?? (niltape ?) ?) >Ht2 #i #Hi 
cases (le_to_or_lt_eq … (le_S_S_to_le … Hi)) -Hi #Hi
  [cases (le_to_or_lt_eq … (le_S_S_to_le … Hi)) -Hi #Hi
    [cases (le_to_or_lt_eq … (le_S_S_to_le … Hi)) -Hi #Hi
      [@False_ind /2/
      |>Hi >obj_low_tapes >nth_change_vec //
       >Ht1 >obj_low_tapes >Hstep @map_action 
      ]
    |>Hi >cfg_low_tapes >nth_change_vec_neq 
      [|% whd in ⊢ (??%?→?);  #H destruct (H)]
     >nth_change_vec // >Hnew_state @eq_f @eq_f >Hnew_tape 
     @eq_f2 [|2:%] >Ht1 >obj_low_tapes >map_move_mono >low_char_current %
    ]
  |(* program tapes do not change *)
   >Hi >prg_low_tapes 
   >nth_change_vec_neq [|% whd in ⊢ (??%?→?);  #H destruct (H)]
   >nth_change_vec_neq [|% whd in ⊢ (??%?→?);  #H destruct (H)]
   >Ht1 >prg_low_tapes //
  ]
qed.

lemma sem_unistep : ∀M.unistep ⊨ R_unistep_high M.
#M @(Realize_to_Realize … (R_unistep_equiv …)) //
qed.
