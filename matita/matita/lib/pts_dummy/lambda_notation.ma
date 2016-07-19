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

(* NOTATION FOR THE LAMBDA CALCULUS *)
(* equivalence, invariance *)

notation "hvbox(a break ≅ b)" 
  non associative with precedence 45
  for @{'Eq $a $b}.

notation "hvbox(a break (≅ ^ term 90 c) b)"
  non associative with precedence 45
  for @{'Eq1 $c $a $b}.

notation "hbox(! term 55 a)"
  non associative with precedence 55
  for @{'Invariant $a}.

notation "hbox((! ^ term 90 b) term 55 a)"
  non associative with precedence 55
  for @{'Invariant1 $a $b}.

(* lifting, substitution *)

notation "hvbox(↑ [ p break , k ] break t)"
   non associative with precedence 55
   for @{'Lift1 $p $k $t}.

notation "hvbox(M break [ / l ])"
   non associative with precedence 90
   for @{'Subst $M $l}.

notation "hvbox(M break [ k ≝ N ])" 
   non associative with precedence 90
   for @{'Subst1 $M $k $N}.

(* type judgements *)

notation "hvbox(G break  ⊢ A break : B)"
   non associative with precedence 45
   for @{'TJ $G $A $B}.

notation "hvbox(G break  ⊢ A break ÷ B)"
   non associative with precedence 45
   for @{'TJ0 $G $A $B}.

(* interpretations *)

notation "hvbox(║T║)"
   non associative with precedence 55
   for @{'IInt $T}.

notation "hvbox(║T║ break _ [E])"
   non associative with precedence 55
   for @{'IInt1 $T $E}.

notation "hvbox(║T║ break _ [E1 break , E2])"
   non associative with precedence 55
   for @{'IInt2 $T $E1 $E2}.

notation "hvbox(║T║ * break _ [E])"
   non associative with precedence 55
   for @{'IIntS1 $T $E}.

notation "hvbox(〚T〛)"
   non associative with precedence 55
   for @{'EInt $T}.

notation "hvbox(〚T〛 break _ [E])"
   non associative with precedence 55
   for @{'EInt1 $T $E}.

notation "hvbox(〚T〛 break _ [E1 break , E2])"
   non associative with precedence 55
   for @{'EInt2 $T $E1 $E2}.

notation "hvbox(《T》)"
   non associative with precedence 55
   for @{'XInt $T}.

notation "hvbox(《T》 break _ [E])"
   non associative with precedence 55
   for @{'XInt1 $T $E}.

notation "hvbox(《T》 break _ [E1 break , E2])"
   non associative with precedence 55
   for @{'XInt2 $T $E1 $E2}.

notation "hvbox(𝕂{G})"
   non associative with precedence 55
   for @{'IK $G}.

notation "hvbox(𝕂{T} break _ [G])"
   non associative with precedence 55
   for @{'IK $T $G}.
