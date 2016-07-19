(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/lists/list.ma".
include "pts_dummy/lambda_notation.ma".

inductive T : Type[0] ≝
  | Sort: nat → T     (* starts from 0 *)
  | Rel: nat → T      (* starts from 0 *)
  | App: T → T → T    (* function, argument *)
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T   (* type, body *)
  | D: T → T → T      (* dummy term, type *)
.

(* Appl F l generalizes App applying F to a list of arguments
 * The head of l is applied first
 *)
let rec Appl F l on l ≝ match l with 
   [ nil ⇒ F
   | cons A D ⇒ Appl (App F A) D  
   ].

lemma appl_append: ∀N,l,M. Appl M (l @ [N]) = App (Appl M l) N.
#N #l elim l normalize // 
qed.

(*
let rec is_dummy t ≝ match t with
   [ Sort _     ⇒ false
   | Rel _      ⇒ false
   | App M _    ⇒ is_dummy M
   | Lambda _ M ⇒ is_dummy M
   | Prod _ _   ⇒ false       (* not so sure yet *)
   | D _        ⇒ true
   ].
*)

(* neutral terms 
   secondo me questa definzione non va qui, comunque la
   estendo al caso dummy *)
inductive neutral: T → Prop ≝
   | neutral_sort: ∀n.neutral (Sort n)
   | neutral_rel: ∀i.neutral (Rel i)
   | neutral_app: ∀M,N.neutral (App M N)
   | neutral_dummy: ∀M,N.neutral (D M N)
.
