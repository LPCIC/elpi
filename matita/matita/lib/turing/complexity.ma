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

(* this no longer works: TODO 
(* time *) 
let rec time_of sig (M:TM sig) a b (p:computation sig M a b) on p ≝
  match p with 
   [ empty x ⇒ 0
   | more a c b h tl ⇒ S (time_of sig M c b tl)
   ]
.

definition ComputeB_in_time ≝ λsig.λM:TM sig.λA:(list sig) → bool.λf.
  ∀l.∃c.∃p:computation sig M (init sig M l) c.
   time_of … p ≤ f (|l|) ∧
   (stop sig M c = true) ∧ (isnilb ? (out ?? c) = false).
*)
(* Le macchine di Turing sono a Type[1], che vorrebbe un nuovo 
esistenziale.  

inductive Ex (A:Type[1]) (P:A → Prop) : Prop ≝
    Ex_intro: ∀ x:A. P x →  Ex A P.
    
interpretation "Exists" 'exists x = (Ex ? x).

definition DTIME ≝ λsig:FinSet. λL: list sig → bool. λf.
∃M:TM sig. ComputeB sig M L ∧ ∃c. Time_Bound sig M (λx.c + c*(f x)).
*)
(* this no longer works: TODO 
inductive DTIME (sig:FinSet) (A:list sig → bool) (f:nat→nat) : Type[1] ≝ 
| DTIME_intro: ∀M:TM sig.∀c.
    ComputeB_in_time sig M A (λx.c + c*(f x)) → DTIME sig A f.
*)
(* space complexity *) 

definition size_of_tape ≝ λsig.λtp: tape sig.|left sig tp|+|right sig tp|.

definition size_of_tapes ≝ λsig.λn.λtps: Vector (tape sig) n.
foldr ?? (λtp.λacc.max (size_of_tape sig tp) acc) 0 tps.
(* this no longer works: TODO 
definition size_of_config ≝ λsig.λM.λc.
  size_of_tapes sig (S (tapes_no sig M)) (tapes sig M c).

let rec space_of sig (M:TM sig) ci cf (p:computation sig M ci cf) on p ≝
  match p with 
   [ empty a ⇒ size_of_config sig M a
   | more a c b h tl ⇒ max (size_of_config sig M a) (space_of sig M c b tl)
   ]
.

definition ComputeB_in_space ≝ λsig.λM:TM sig.λA:(list sig) → bool.λf.
  ∀l.∃c.∃p:computation sig M (init sig M l) c.
   space_of … p ≤ f (|l|) ∧
   (stop sig M c = true) ∧ (isnilb ? (out ?? c) = false).

inductive DSPACE (sig:FinSet) (A:list sig → bool) (f:nat→nat) : Type[1] ≝ 
| DTIME_intro: ∀M:TM sig.∀c.
    ComputeB_in_space sig M A (λx.c + c*(f x)) → DSPACE sig A f.
*)