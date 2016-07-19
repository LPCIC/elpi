(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "nat/plus.ma".

definition hole : ∀A:Type.A → A ≝ λA.λx.x.
definition id : ∀A:Type.A → A ≝ λA.λx.x.

(* Common case in dama, reduction with metas
inductive list : Type := nil : list | cons : nat -> list -> list.
let rec len l := match l with [ nil => O | cons _ l => S (len l) ].
axiom lt : nat -> nat -> Prop.
axiom foo : ∀x. Not (lt (hole ? x) (hole ? O)) = (lt x (len nil) -> False).
*) 

(* meta1 Vs meta2 with different contexts
axiom foo: 
  ∀P:Type.∀f:P→P→Prop.∀x:P.
   (λw. ((∀e:P.f x (w x)) = (∀y:P. f x (hole ? y)))) 
   (λw:P.hole ? w). 
*)

(* meta1 Vs meta1 with different local contexts
axiom foo: 
  ∀P:Type.∀f:P→P→P.∀x,y:P. 
    (λw.(f x (w x) = f x (w y))) (λw:P.hole ? w).
*)

(* meta Vs term && term Vs meta with different local ctx
axiom foo: 
  ∀P:Type.∀f:P→P→P.∀x,y:P.
    (λw.(f (w x) (hole ? x) = f x (w y))) (λw:P.hole ? w).
*)

(* occur check
axiom foo: 
  ∀P:Type.∀f:P→P→P.∀x,y:P.
    (λw.(f x (f (w x) x) = f x (w y))) (λw:P.hole ? w).
*)

(* unifying the type of (y ?) with (Q x) we instantiate ? to x
axiom foo: 
  ∀P:Type.∀Q:P→Type.∀f:∀x:P.Q x→P→P.∀x:P.∀y:∀x.Q x.
    (λw.(f w (y w) x = (id ? f) x (hole ? (y x)) x)) (hole ? x).
*)  
   
alias num (instance 0) = "natural number".
axiom foo: (100+111) = (100+110). 


    (id ?(id ?(id ?(id ? (100+100))))) =
    (id ?(id ?(id ?(id ? (99+100))))).[3:
    apply (refl_eq nat (id ?(id ?(id ?(id ? (98+102+?))))));

axiom foo: (λx,y.(λz. z (x+y) + z x) (λw:nat.hole ? w)) = λx,y.x. (* OK *)
axiom foo: (λx,y.(λz. z x + z (x+y)) (λw:nat.hole ? w)) = λx,y.x. (* KO, delift rels only *) 
 


axiom foo: (λx,y.(λz. z x + z y) (λw:nat.hole ? w)) = λx,y.x. (* OK *) 

