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

include "turing/multi_universal/alphabet.ma".
include "turing/mono.ma".

(*************************** normal Turing Machines ***************************)

(* A normal turing machine is just an ordinary machine where:
  1. the tape alphabet is bool
  2. the finite state are supposed to be an initial segment of the natural 
     numbers. 
  Formally, it is specified by a record with the number n of states, a proof
  that n is positive, the transition function and the halting function.
*)

definition trans_source ≝ λn.
  FinProd (initN n) (FinOption FinBool).
  
definition trans_target ≝ λn.
  FinProd (FinProd (initN n) (FinOption FinBool)) FinMove.

record normalTM : Type[0] ≝ 
{ no_states : nat;
  pos_no_states : (0 < no_states); 
  ntrans : trans_source no_states → trans_target no_states;
  nhalt : initN no_states → bool
}.

lemma decomp_target : ∀n.∀tg: trans_target n. 
  ∃qout,cout,m. tg = 〈qout,cout,m〉.
#n * * #q #c #m %{q} %{c} %{m} //
qed.

(* A normal machine is just a special case of Turing Machine. *)

definition nstart_state ≝ λM.mk_Sig ?? 0 (pos_no_states M).

definition normalTM_to_TM ≝ λM:normalTM.
  mk_TM FinBool (initN (no_states M)) 
   (ntrans M) (nstart_state M) (nhalt M).

coercion normalTM_to_TM.

definition nconfig ≝ λn. config FinBool (initN n).

(* A normal machine has a non empty graph *)

definition sample_input: ∀M.trans_source (no_states M).
#M % [@(nstart_state M) | %]
qed.

lemma nTM_nog: ∀M. graph_enum ?? (ntrans M) ≠ [ ].
#M % #H lapply(graph_enum_complete ?? (ntrans M) (sample_input M) ? (refl ??))
>H normalize #Hd destruct
qed.

(******************************** tuples **************************************)

(* By general results on FinSets we know that every function f between two 
finite sets A and B can be described by means of a finite graph of pairs
〈a,f a〉. Hence, the transition function of a normal turing machine can be
described by a finite set of tuples 〈i,c〉,〈j,action〉〉 of the following type:
  (Nat_to n × (option FinBool)) × (Nat_to n × (option FinBool) × move).  
Unfortunately this description is not suitable for a Universal Machine, since
such a machine must work with a fixed alphabet, while the size on n is unknown.
Hence, we must pass from natural numbers to a representation for them on a 
finitary, e.g. binary, alphabet. In general, we shall associate
to a pair 〈〈i,x〉,〈j,y,m〉〉 a tuple with the following syntactical structure
           | w_i x w_j y m
where 
1. "|" is a special character used to separate tuples
2. w_i and w_j are list of booleans representing the states $i$ and $j$; 
3. x and y are encoding 
4. finally, m ...
*)

definition mk_tuple ≝ λqin,cin,qout,cout,mv.
  bar::qin@cin::qout@[cout;mv].

definition tuple_TM : nat → list unialpha → Prop ≝ 
 λn,t.∃qin,cin,qout,cout,mv.
 only_bits qin ∧ only_bits qout ∧ cin ≠ bar ∧ cout ≠ bar ∧ mv ≠ bar ∧
 |qin| = n ∧ |qout| = n ∧
 t = mk_tuple qin cin qout cout mv. 

(***************************** state encoding *********************************)
(* p < n is represented with a list of bits of lenght n with the p-th bit from 
left set to 1. An additional intial bit is set to 1 if the state is final and
to 0 otherwise. *)
 
let rec to_bitlist n p: list bool ≝
  match n with [ O ⇒ [ ] | S q ⇒ (eqb p q)::to_bitlist q p].
  
let rec from_bitlist l ≝
  match l with 
  [ nil ⇒ 0 (* assert false *)
  | cons b tl ⇒ if b then |tl| else from_bitlist tl].

lemma bitlist_length: ∀n,p.|to_bitlist n p| = n.
#n elim n normalize // 
qed.

lemma bitlist_inv1: ∀n,p.p<n → from_bitlist (to_bitlist n p) = p.
#n elim n normalize -n
  [#p #abs @False_ind /2/
  |#n #Hind #p #lepn 
   cases (le_to_or_lt_eq … (le_S_S_to_le … lepn))
    [#ltpn lapply (lt_to_not_eq … ltpn) #Hpn
     >(not_eq_to_eqb_false … Hpn) normalize @Hind @ltpn
    |#Heq >(eq_to_eqb_true … Heq) normalize <Heq //
    ]
  ]
qed.

lemma bitlist_lt: ∀l. 0 < |l| → from_bitlist l < |l|.
#l elim l normalize // #b #tl #Hind cases b normalize //
#Htl cases (le_to_or_lt_eq … (le_S_S_to_le … Htl)) -Htl #Htl
  [@le_S_S @lt_to_le @Hind //  
  |cut (tl=[ ]) [/2 by append_l2_injective/] #eqtl >eqtl @le_n
  ]
qed.

definition nat_of: ∀n. Nat_to n → nat.
#n normalize * #p #_ @p
qed. 

definition bits_of_state ≝ λn.λh:Nat_to n → bool.λs:Nat_to n.
   map ? unialpha (λx.bit x) (h s::(to_bitlist n (nat_of n s))).

lemma only_bits_bits_of_state : ∀n,h,p. only_bits (bits_of_state n h p).
#n #h #p #x whd in match (bits_of_state n h p);
#H cases H -H 
  [#H >H %
  |elim (to_bitlist n (nat_of n p))
    [@False_ind |#b #l #Hind #H cases H -H #H [>H % |@Hind @H ]]
  ]
qed.

(******************************** action encoding *****************************)

definition low_char ≝ λc. 
  match c with 
    [ None ⇒ null
    | Some b ⇒ bit b
    ].
    
definition low_mv ≝ λm. 
  match m with 
  [ R ⇒ bit true
  | L ⇒ bit false
  | N ⇒ null
  ].

lemma injective_low_char: injective … low_char.
#c1 #c2 cases c1 cases c2 normalize //
  [#b1 #H destruct
  |#b1 #H destruct
  |#b1 #b2 #H destruct //
  ]
qed.   

lemma injective_low_mv: injective … low_mv.
#m1 #m2 cases m1 cases m2 // normalize #H destruct
qed.
   
(******************************** tuple encoding ******************************)
definition tuple_type ≝ λn.
 (Nat_to n × (option FinBool)) × (Nat_to n × (option FinBool) × move).  

definition tuple_encoding ≝ λn.λh:Nat_to n→bool. 
  λp:tuple_type n.
  let 〈inp,outp〉 ≝ p in
  let 〈q,a〉 ≝ inp in
  let 〈qn,an,m〉 ≝ outp in
  let qin ≝ bits_of_state n h q in
  let qout ≝ bits_of_state n h qn in
  let cin ≝ low_char a in
  let cout ≝ low_char an in
  let mv ≝ low_mv m in
  mk_tuple qin cin qout cout mv.

lemma is_tuple: ∀n,h,p. tuple_TM (S n) (tuple_encoding n h p).
#n #h * * #q #a * * #qn #an #m
%{(bits_of_state n h q)} %{(low_char a)} 
%{(bits_of_state n h qn)} %{(low_char an)} %{(low_mv m)} 
% // % 
  [%[%[%[%[% /2/ |% cases a normalize [|#b] #H destruct]
        |% cases an normalize [|#b] #H destruct]
      |% cases m normalize #H destruct]
    |>length_map normalize @eq_f //]
  |>length_map normalize @eq_f //]
qed. 

definition tuple_length ≝ λn.2*n+4.

lemma length_of_tuple: ∀n,t. tuple_TM n t → 
  |t| = tuple_length n.
#n #t * #qin * #cin * #qout * #cout * #mv *** #_ #Hqin #Hqout #eqt 
>eqt normalize >length_append >Hqin -Hqin normalize >length_append 
normalize >Hqout //
qed.

definition tuples_list ≝ λn.λh.map … (λp.tuple_encoding n h p).




