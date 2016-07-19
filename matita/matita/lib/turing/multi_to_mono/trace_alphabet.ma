(* This file contains the definition of the alphabet for the mono-tape machine
simulating a multi-tape machine, and a library of functions operating on them *)

include "basics/vector_finset.ma".

(* a multi_sig characheter is composed by n+1 sub-characters: n for each tape 
of a multitape machine.  
We extend the tape alphabet with a special symbol None to pad shorter tapes.
For the moment, the actual content of the tape alphabet is left unspecifed, 
but we shall need characters to store states and moves of the multitape 
machines and to mark the head position *)

definition sig_ext ≝ λsig. FinOption sig.
definition blank : ∀sig.sig_ext sig ≝ λsig. None sig.

(* definition head : ∀sig.sig_ext sig ≝ λsig. inl … true. *)

definition multi_sig ≝ λsig:FinSet.λn.FinVector (sig_ext sig) n.

(* a character containing blank characters in each trace *)
let rec all_blanks sig n on n : multi_sig sig n ≝ 
  match n with
  [ O ⇒ Vector_of_list ? []
  | S m ⇒ vec_cons ? (blank ?) m (all_blanks sig m)
  ].

lemma blank_all_blanks: ∀sig,n,i.
  nth i ? (vec … (all_blanks sig n)) (blank sig) = blank ?.
#sig #n elim n normalize [#i >nth_nil // |#m #Hind #i cases i // #j @Hind ]
qed.

lemma all_blank_n: ∀sig,n.
  nth n ? (vec … (all_blanks sig n)) (blank sig) = blank ?.
#sig #n @blank_all_blanks 
qed.

(* boolen test functions *)

definition not_blank ≝ λsig,n,i.λc:multi_sig sig n.
  ¬(nth i ? (vec … c) (blank ?))==blank ?.

(*
definition no_head ≝ λsig,n.λc:multi_sig sig n.
  ¬((nth n ? (vec … c) (blank ?))==head ?).
    
lemma no_head_true: ∀sig,n,a. 
  nth n ? (vec … n a) (blank sig) ≠ head ? → no_head … a = true.
#sig #n #a normalize cases (nth n ? (vec … n a) (blank sig))
normalize // * normalize // * #H @False_ind @H //
qed.

lemma no_head_false: ∀sig,n,a. 
  nth n ? (vec … n a) (blank sig) = head ? → no_head … a = false.
#sig #n #a #H normalize >H //  
qed. *)

(**************************** extract the i-th trace **************************)
definition trace ≝ λsig,n,i,l. 
  map ?? (λa. nth i ? (vec … n a) (blank sig)) l.

lemma trace_def : ∀sig,n,i,l. 
  trace sig n i l = map ?? (λa. nth i ? (vec … n a) (blank sig)) l.
// qed.

lemma hd_trace:  ∀sig,n,i,l. 
  hd ? (trace sig n i l) (blank ?) = 
    nth i ? (hd ? l (all_blanks … )) (blank ?).
#sig #n #i #l elim l // normalize >blank_all_blanks % 
qed.
 
lemma tail_trace:  ∀sig,n,i,l. 
  tail ? (trace sig n i l) = trace sig n i (tail ? l).
#sig #n #i #l elim l // 
qed.

lemma trace_append :  ∀sig,n,i,l1,l2. 
  trace sig n i (l1 @ l2) = trace sig n i l1 @ trace sig n i l2.
#sig #n #i #l1 #l2 elim l1 // #a #tl #Hind normalize >Hind //
qed.

lemma trace_reverse : ∀sig,n,i,l. 
  trace sig n i (reverse ? l) = reverse (sig_ext sig) (trace sig n i l).
#sig #n #i #l elim l //
#a #tl #Hind whd in match (trace ??? (a::tl)); >reverse_cons >reverse_cons
>trace_append >Hind // 
qed.

lemma length_trace: ∀sig,n,i,l.
  |trace sig n i l| = |l|.
#sig #n #i #l elim l // #a #tl #Hind normalize @eq_f @Hind
qed. 

lemma nth_trace : ∀sig,n,i,j,l.
  nth j ? (trace sig n i l) (blank ?) = 
    nth i ? (nth j ? l (all_blanks sig n)) (blank ?).
#sig #n #i #j elim j
  [#l cases l normalize // >blank_all_blanks //
  |-j #j #Hind #l whd in match (nth ????); whd in match (nth ????);
   cases l 
    [normalize >nth_nil >nth_nil >blank_all_blanks //
    |#a #tl normalize @Hind]
  ]
qed.

(*
definition no_head_in ≝ λsig,n,l. 
  ∀x. mem ? x (trace sig n n l) → x ≠ head ?.
*)

(* some lemmas over lists, to be moved *)
lemma injective_append_l: ∀A,l. injective ?? (append A l).
#A #l elim l 
  [#l1 #l2 normalize //
  |#a #tl #Hind #l1 #l2 normalize #H @Hind @(cons_injective_r … H)
  ]
qed.

lemma injective_append_r: ∀A,l. injective ?? (λl1.append A l1 l).
#A #l #l1 #l2 #H 
cut (reverse ? (l1@l) = reverse ? (l2@l)) [//] 
>reverse_append >reverse_append #Hrev
lapply (injective_append_l … Hrev) -Hrev #Hrev 
<(reverse_reverse … l1) <(reverse_reverse … l2) //
qed.

lemma reverse_map: ∀A,B,f,l.
  reverse B (map … f l) = map … f (reverse A l).
#A #B #f #l elim l //
#a #l #Hind >reverse_cons >reverse_cons <map_append >Hind //
qed.
  
lemma injective_reverse: ∀A. injective ?? (reverse A).
#A #l1 #l2 #H <(reverse_reverse … l1) <(reverse_reverse … l2) //
qed.

lemma first_P_to_eq : ∀A:Type[0].∀P:A→Prop.∀l1,l2,l3,l4,a1,a2.
  l1@a1::l2 = l3@a2::l4 → (∀x. mem A x l1 → P x) → (∀x. mem A x l2 → P x) →
  ¬ P a1 → ¬ P a2 → l1 = l3 ∧ a1::l2 = a2::l4.
#A #P #l1 elim l1
  [#l2 * 
    [#l4 #a1 #a2 normalize #H destruct /2/
    |#c #tl #l4 #a1 #a2 normalize #H destruct
     #_ #H #_ #H1 @False_ind @(absurd ?? H1) @H @mem_append_l2 %1 // 
    ]
  |#b #tl1 #Hind #l2 *
    [#l4 #a1 #a2 normalize #H destruct 
     #H1 #_ #_ #H2 @False_ind @(absurd ?? H2) @H1 %1 //
    |#c #tl2 #l4 #a1 #a2 normalize #H1 #H2 #H3 #H4 #H5 
     lapply (Hind l2 tl2 l4 … H4 H5) 
      [destruct @H3 |#x #H6 @H2 %2 // | destruct (H1) //
      |* #H6 #H7 % // >H7 in H1; #H1 @(injective_append_r … (a2::l4)) @H1
    ]
  ]
qed.
  
lemma nth_to_eq: ∀A,l1,l2,a. |l1| = |l2| →
  (∀i. nth i A l1 a = nth i A l2 a) → l1 = l2.
#A #l1 elim l1
  [* // #a #tl #d normalize #H destruct (H)
  |#a #tl #Hind *
    [#d normalize #H destruct (H)
    |#b #tl1 #d #Hlen #Hnth @eq_f2 
      [@(Hnth 0) | @(Hind tl1 d) [@injective_S @Hlen | #i @(Hnth (S i)) ]]
    ]
  ]
qed.

lemma nth_extended: ∀A,i,l,a. 
  nth i A l a = nth i A (l@[a]) a.
#A #i elim i [* // |#j #Hind * // #b #tl #a normalize @Hind]
qed.  

(******************************* shifting a trace *****************************)

(* (shift_i sig n i a b) replace the i-th trace of the character a with the
i-th trace of b *)

definition shift_i ≝ λsig,n,i.λa,b:Vector (sig_ext sig) n.
  change_vec (sig_ext sig) n a (nth i ? b (blank ?)) i.

(* given two strings v1 and v2 of the mono-tape machine, (shift_l … i v1 v2) 
asserts that v1 is obtained from v2 by shifting_left the i-trace *)   

definition shift_l ≝ λsig,n,i,v1,v2.  (* multi_sig sig n *) 
  |v1| = |v2| ∧ 
  ∀j.nth j ? v2 (all_blanks sig n) = 
      change_vec ? n (nth j ? v1 (all_blanks sig n)) 
        (nth i ? (vec … (nth (S j) ? v1 (all_blanks sig n))) (blank ?)) i.

(* supposing (shift_l … i v1 v2), the i-th trace of v2 is equal to the tail of
the i-th trace of v1, plus a trailing blank *)
  
lemma trace_shift: ∀sig,n,i,v1,v2. i < n → 0 < |v1| →
  shift_l sig n i v1 v2 → trace ? n i v2 = tail ? (trace ? n i v1)@[blank sig].
#sig #n #i #v1 #v2 #lein #Hlen * #Hlen1 #Hnth @(nth_to_eq … (blank ?))
  [>length_trace <Hlen1 generalize in match Hlen; cases v1  
    [normalize #H @(le_n_O_elim … H) // 
    |#b #tl #_ normalize >length_append >length_trace normalize //
    ]
  |#j >nth_trace >Hnth >nth_change_vec // >tail_trace 
   cut (trace ? n i [all_blanks sig n] = [blank sig]) 
     [normalize >blank_all_blanks //] 
   #Hcut <Hcut <trace_append >nth_trace 
   <nth_extended //
  ]
qed.

(* supposing (shift_l … i v1 v2), and j≠i, the j-th trace of v2 is equal to the 
j-th trace of v1 *)

lemma trace_shift_neq: ∀sig,n,i,j,v1,v2. i < n → 0 < |v1| → i ≠ j →
  shift_l sig n i v1 v2 → trace ? n j v2 = trace ? n j v1.
#sig #n #i #j #v1 #v2 #lein #Hlen #Hneq * #Hlen1 #Hnth @(nth_to_eq … (blank ?))
  [>length_trace >length_trace @sym_eq @Hlen1
  |#k >nth_trace >Hnth >nth_change_vec_neq // >nth_trace // 
  ]
qed.

(******************************************************************************)

let rec to_blank sig l on l ≝
  match l with
  [ nil ⇒  [ ]
  | cons a tl ⇒ 
      if a == blank sig then [ ] else a::(to_blank sig tl)]. 
      
let rec after_blank sig l on l ≝
  match l with
  [ nil ⇒  [ ]
  | cons a tl ⇒ 
      if a == blank sig then (a::tl) else (after_blank sig tl)]. 
      
definition to_blank_i ≝ λsig,n,i,l. to_blank ? (trace sig n i l).

lemma to_blank_i_def : ∀sig,n,i,l. 
  to_blank_i sig n i l = to_blank ? (trace sig n i l).
// qed.

lemma to_blank_cons_b : ∀sig,n,i,a,l.
  nth i ? (vec … n a) (blank sig) = blank ? →
  to_blank_i sig n i (a::l) = [ ].
#sig #n #i #a #l #H whd in match (to_blank_i ????);
>(\b H) //
qed.      

lemma to_blank_cons_nb: ∀sig,n,i,a,l.
  nth i ? (vec … n a) (blank sig) ≠ blank ? →
  to_blank_i sig n i (a::l) = 
    nth i ? (vec … n a) (blank sig)::(to_blank_i sig n i l).
#sig #n #i #a #l #H whd in match (to_blank_i ????);
>(\bf H) //
qed.

axiom to_blank_hd : ∀sig,n,a,b,l1,l2. 
  (∀i. i < n → to_blank_i sig n i (a::l1) = to_blank_i sig n i (b::l2)) → a = b.

lemma to_blank_i_ext : ∀sig,n,i,l.
  to_blank_i sig n i l = to_blank_i sig n i (l@[all_blanks …]).
#sig #n #i #l elim l
  [@sym_eq @to_blank_cons_b @blank_all_blanks
  |#a #tl #Hind whd in match (to_blank_i ????); >Hind <to_blank_i_def >Hind %
  ]
qed. 
  
lemma to_blank_hd_cons : ∀sig,n,i,l1,l2.
  to_blank_i sig n i (l1@l2) = 
    to_blank_i … i (l1@(hd … l2 (all_blanks …))::tail … l2).
#sig #n #i #l1 #l2 cases l2
  [whd in match (hd ???); whd in match (tail ??); >append_nil @to_blank_i_ext 
  |#a #tl % 
  ]
qed.

lemma to_blank_i_chop : ∀sig,n,i,a,l1,l2.
 (nth i ? (vec … a) (blank ?))= blank ? → 
 to_blank_i sig n i (l1@a::l2) = to_blank_i sig n i l1.
#sig #n #i #a #l1 elim l1
  [#l2 #H @to_blank_cons_b //
  |#x #tl #Hind #l2 #H whd in match (to_blank_i ????); 
   >(Hind l2 H) <to_blank_i_def >(Hind l2 H) %
  ]
qed. 
    




