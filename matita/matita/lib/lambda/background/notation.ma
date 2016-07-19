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

(* GENERIC NOTATION *********************************************************)

(* Note: this should go to core_notation *)
notation "⊥"
  non associative with precedence 90
  for @{'false}.

(* Note: this should go to core_notation *)
notation "⊤"
  non associative with precedence 90
  for @{'true}.

(* Note: this should go to core_notation *)
notation "hvbox(a break ≺ b)"
   non associative with precedence 45
   for @{ 'prec $a $b }.

notation "hvbox( # term 90 i )"
 non associative with precedence 46
 for @{ 'VariableReferenceByIndex $i }.

notation "hvbox( { term 46 b } # break term 90 i )"
 non associative with precedence 46
 for @{ 'VariableReferenceByIndex $b $i }.

notation "hvbox( 𝛌 . term 46 A )"
   non associative with precedence 46
   for @{ 'Abstraction $A }.

notation "hvbox( { term 46 b } 𝛌 . break term 46 T)"
   non associative with precedence 46
   for @{ 'Abstraction $b $T }.

notation "hvbox( 𝛌 term 46 d . break term 46 A )"
   non associative with precedence 46
   for @{ 'AnnotatedAbstraction $d $A }.

notation "hvbox( @ term 46 C . break term 46 A )"
   non associative with precedence 46
   for @{ 'Application $C $A }.

notation "hvbox( { term 46 b } @ break term 46 V . break term 46 T )"
   non associative with precedence 46
   for @{ 'Application $b $V $T }.

notation "hvbox( ↑ [ term 46 d , break term 46 h ] break term 46 M )"
   non associative with precedence 46
   for @{ 'Lift $h $d $M }.

notation > "hvbox( ↑ [ term 46 h ] break term 46 M )"
   non associative with precedence 46
   for @{ 'Lift $h 0 $M }.

notation > "hvbox( ↑ term 46 M )"
   non associative with precedence 46
   for @{ 'Lift 1 0 $M }.

(* Note: the notation with "/" does not work *)
notation "hvbox( [ term 46 d break ↙ term 46 N ] break term 46 M )"
   non associative with precedence 46
   for @{ 'DSubst $N $d $M }.

notation > "hvbox( [ ↙ term 46 N ] break term 46 M )"
   non associative with precedence 46
   for @{ 'DSubst $N 0 $M }.

(* Note: we do not use → since it is reserved by CIC *)
notation "hvbox( M break ↦ term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRed $M $N }.

notation "hvbox( M break ↦ [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRed $M $p $N }.

notation "hvbox( M break ↦* term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRedStar $M $N }.

notation "hvbox( M break ↦* [ term 46 s ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRedStar $M $s $N }.

notation "hvbox( M break ⤇ term 46 N )"
   non associative with precedence 45
   for @{ 'ParRed $M $N }.

notation "hvbox( M break ⤇* term 46 N )"
   non associative with precedence 45
   for @{ 'ParRedStar $M $N }.
