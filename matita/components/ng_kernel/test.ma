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

(*
let rec f n := 
  match n with
  [ O => O
  | S m => let rec g x := 
             match x with
             [ O => f m
             | S q => 
                  let rec h y := 
                    match y with 
                    [ O => f m + g q
                    | S w => h w]
                  in
                    h q] 
           in 
             g m].
*)

let rec f n := 
  match n with
  [ O => O
  | S m => g m
  ]
and g m :=
 match m with
  [ O => O
  | S n => f n
  ].