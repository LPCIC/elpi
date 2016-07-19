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

include "turing/turing.ma". 

(* Oracle machines *)

record TM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  tapes_no: nat; (* additional working tapes *)
  trans : states × (Vector (option sig) (S tapes_no)) → 
    states  × (Vector (sig × move) (S tapes_no)) × (option sig) ;
  output: list sig;
  start: states;
  halt : states → bool
}.

inductive oracle_states :Type[0] ≝
  | query : oracle_states
  | yes : oracle_states
  | no : oracle_states.

record config (sig:FinSet) (M:TM sig): Type[0] ≝
{ state : states sig M;
  query : list sig;
  tapes : Vector (tape sig) (S (tapes_no sig M));
  out : list sig
}.

definition option_hd ≝ λA.λl:list A.
  match l with
  [nil ⇒ None ?
  |cons a _ ⇒ Some ? a
  ].
(* this no longer works: TODO 
definition tape_move ≝ λsig.λt: tape sig.λm:sig × move.
  match \snd m with
  [ R ⇒ mk_tape sig ((\fst m)::(left ? t)) (tail ? (right ? t))
  | L ⇒ mk_tape sig (tail ? (left ? t)) ((\fst m)::(right ? t))
  | N ⇒ mk_tape sig (left ? t) ((\fst m)::(tail ? (right ? t)))
  ].
*)
definition current_chars ≝ λsig.λM:TM sig.λc:config sig M.
  vec_map ?? (λt.option_hd ? (right ? t)) (S (tapes_no sig M)) (tapes ?? c).

definition opt_cons ≝ λA.λa:option A.λl:list A.
  match a with
  [ None ⇒ l
  | Some a ⇒ a::l
  ].
(* this no longer works: TODO 
definition step ≝ λsig.λM:TM sig.λc:config sig M.
  let 〈news,mvs,outchar〉 ≝ trans sig M 〈state ?? c,current_chars ?? c〉 in
  mk_config ?? 
    news 
    (pmap_vec ??? (tape_move sig) ? (tapes ?? c) mvs)
    (opt_cons ? outchar (out ?? c)).

definition empty_tapes ≝ λsig.λn.
mk_Vector ? n (make_list (tape sig) (mk_tape sig [] []) n) ?.
elim n // normalize //
qed.

definition init ≝ λsig.λM:TM sig.λi:(list sig).
  mk_config ??
    (start sig M)
    (vec_cons ? (mk_tape sig [] i) ? (empty_tapes sig (tapes_no sig M)))
    [ ].
*)
definition stop ≝ λsig.λM:TM sig.λc:config sig M.
  halt sig M (state sig M c).

let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].
(* this no longer works: TODO 
(* Compute ? M f states that f is computed by M *)
definition Compute ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  out ?? c = f l.

(* for decision problems, we accept a string if on termination
output is not empty *)

definition ComputeB ≝ λsig.λM:TM sig.λf:(list sig) → bool.
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  (isnilb ? (out ?? c) = false).
*)