(* include "turing/auxiliary_machines.ma". *)

include "turing/multi_to_mono/exec_trace_move.ma".
(* include "turing/turing.ma". *)
  
let rec exec_moves Q sig n i on i : TM (MTA (HC Q n) sig (S n)) ≝
  match i with 
  [ O ⇒ nop ? (* exec_move_i sig n 0 *)
  | S j ⇒ seq ? (exec_moves Q sig n j) (exec_move_i Q sig n j) 
  ].

definition a_moves ≝ 
  λsig,n.λactions: Vector ((option sig) × move) n. 
  vec_map ?? (snd ??) n actions.
  
definition a_chars ≝ 
  λsig,n.λactions: Vector ((option sig) × move) n. 
  vec_map ?? (fst ??) n actions.

definition tape_moves ≝ 
  λsig,n,ts,mvs.
  pmap_vec ??? (tape_move sig) n ts mvs.
  
lemma tape_moves_def : ∀sig,n,ts,mvs.
  tape_moves sig n ts mvs = pmap_vec ??? (tape_move sig) n ts mvs.
// qed.
 
definition tape_writem ≝ 
  λsig,n,ts,chars.
  pmap_vec ??? (tape_write sig) n ts chars.

(*
let rec i_moves a i on i : Vector move i ≝
  match i with 
  [ O ⇒ mk_Vector ? 0 (nil ?) (refl ??)
  | S j ⇒ vec_cons ? (nth j ? a N) j (i_moves a j)
  ]. *)

definition vec_moves ≝ λQ,sig,n,a,i. 
  resize_vec … (get_moves Q sig n a) i N.

axiom vec_moves_cons: ∀Q,sig,n,a,j.j < n → 
 vec_moves Q sig n a (S j) = 
 vec_cons ? (get_move Q ? n a j) j (vec_moves Q sig n a j).

(*
axiom actions_commute : ∀sig,n,ts,actions.
  tape_moves sig n (tape_writem ?? ts (a_chars … actions)) (a_moves … actions) = 
    tape_move_multi ?? ts actions. *)

(* devo rafforzare la semantica, dicendo che i tape non toccati
dalle moves non cambiano *)


definition R_exec_moves ≝ λQ,sig,n,i,t1,t2.
∀a,ls,rs. 
  t1 = midtape ? ls a rs → 
  (∀i.regular_trace (TA (HC Q n) sig) (S n) a ls rs i) → 
  is_head ?? (nth n ? (vec … a) (blank ?)) = true →  
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (MTA (HC Q n) sig (S n)) ls1 a1 rs1 ∧
   (∀i.regular_trace (TA (HC Q n) sig) (S n) a1 ls1 rs1 i) ∧
   (∀j. j < i → j ≤ n →
    rb_trace_i ? (S n) ls1 (vec … a1) rs1 j =
     tape_move ? (rb_trace_i ? (S n) ls (vec … a) rs j) (get_move Q sig n a j)) ∧
    (* tape_moves ?? (readback ? (S n) ls (vec … a) rs i) (vec_moves Q sig n a i) ∧ *)
   (∀j. i ≤ j → j ≤ n → 
    rb_trace_i ? (S n) ls1 (vec … a1) rs1 j = 
      rb_trace_i ? (S n) ls (vec … a) rs j).
     
(* alias id "Realize_to_Realize" = 
  "cic:/matita/turing/mono/Realize_to_Realize.def(13)". *)

(*
lemma nth_readback: ∀sig,n,ls,a,rs,j,i. i < j →
 nth i ? (readback sig n ls a rs j) (niltape ?) = 
   rb_trace_i sig n ls a rs (j - S i).
#sig #n #ls #a #rs #j elim j
  [#i #lti0 @False_ind /2/
  |-j #j #Hind *
    [#_ >minus_S_S <minus_n_O % 
    |#m #Hmj >minus_S_S @Hind @le_S_S_to_le //
    ]
  ]
qed. *)

lemma sem_exec_moves: ∀Q,sig,n,i. i ≤ n → 
  exec_moves Q sig n i ⊨ R_exec_moves Q sig n i.
#Q #sig #n #i elim i 
  [#_ @(Realize_to_Realize … (sem_nop …))
   #t1 #t2 #H #a #ls #rs #Ht1 #Hreg #H1 #H2 #H3 
   %{ls} %{a} %{rs} %[% >H [%[@Ht1|@Hreg]| #j #ltjO @False_ind /2/]|//]
  |#j #Hind #lttj lapply (lt_to_le … lttj) #ltj
   @(sem_seq_app … (Hind ltj) (sem_exec_move_i … lttj)) -Hind
   #int #outt * #t1 * #H1 #H2
   #a #ls #rs #Hint #H3 #H4 #H5 #H6
   lapply (H1 … Hint H3 H4 H5 H6)
   * #ls1 * #a1 * #rs1 * * * #H7 #H8 #H9 #H10
   lapply (reg_inv … (H8 n) ? H4 H5 H6)
    [@H10 [@ltj |@le_n]]
   -H3 -H4 -H5 -H6 * * #H3 #H4 #H5
   lapply (H2 … H7 H8 H3 H4 H5)
   * #ls2 * #a2 * #rs2 * * * #Houtt #Hregout #Hrboutt #Hrbid
   %{ls2} %{a2} %{rs2} 
   cut (∀i. get_move Q sig n a i = get_move Q sig n a1 i)
     [@daemon] #aa1
   %[%[%[@Houtt|@Hregout]
      |#k #ltk cases (le_to_or_lt_eq … ltk) #Hk #lekn
        [>(Hrbid … lekn) [2:@lt_to_not_eq @le_S_S_to_le @Hk]
         @(H9 k ? lekn) @le_S_S_to_le @Hk
        |destruct (Hk) <H10 // @Hrboutt
        ]
      ]
    |#a #Hja #Han >(Hrbid … Han) 
      [@(H10 … Han) @lt_to_le @Hja |@sym_not_eq @lt_to_not_eq @Hja ]
    ]
  ]
qed.
  
