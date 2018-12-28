/*
 * Implementation of a collection of primitive tactics for a 
 * fragment of first-order logic. The proof objects that are built to
 * complement the use of the tactics here are in the form of natural
 * deduction proofs.
 */

module ndtac.

accum_sig goaltypes, ndproofs, logic.

accumulate listmanip.

kind    judgment	type.
kind    answer		type.

type    of_type		proof_object -> bool -> judgment.
type    -->		(list judgment) -> judgment -> goal.

type	yes		answer.

type	exists_e_tac	int -> goal -> goal -> o.
type	or_e_tac	int -> goal -> goal -> o.
type	forall_e_query	int -> goal -> goal -> o.
type	forall_e_tac	int -> goal -> goal -> o.
type	fchain_tac	int -> goal -> goal -> o.
type	bchain_tac	int -> goal -> goal -> o.
type	imp_e_retain	int -> goal -> goal -> o.
type	imp_e_tac	int -> goal -> goal -> o.
type	and_e_tac	int -> goal -> goal -> o.
type	exists_i_query	goal -> goal -> o.
type	exists_i_tac	goal -> goal -> o.
type	forall_i_tac	goal -> goal -> o.
type	imp_i_tac	goal -> goal -> o.
type	or_i2_tac	goal -> goal -> o.
type	or_i1_tac	goal -> goal -> o.
type	and_i_tac	goal -> goal -> o.
type	close_tacn	int -> goal -> goal -> o.
type	close_tac	goal -> goal -> o.

infix   of_type 120.
infix   --> 110.

close_tac (Gamma --> (P of_type A)) truegoal :-
  member (P of_type A) Gamma.

close_tacn N (Gamma --> P of_type A) truegoal :-
  nth_item N (P of_type A) Gamma.

and_i_tac (Gamma --> (and_i P1 P2) of_type A and B)
          (andgoal (Gamma --> P1 of_type A) (Gamma --> P2 of_type B)).

or_i1_tac (Gamma --> (or_i1 P) of_type A or B)
          (Gamma --> P of_type A).

or_i2_tac (Gamma --> (or_i2 P) of_type A or B)
          (Gamma --> P of_type B).

imp_i_tac (Gamma --> (imp_i P) of_type A imp B)
          (allgoal PA\ (((PA of_type A) :: Gamma) --> (P PA) of_type B)).

forall_i_tac (Gamma --> (forall_i P) of_type forall A)
             (allgoal T\ (Gamma --> (P T) of_type (A T))).

exists_i_tac (Gamma --> (exists_i T P) of_type some A)
             (Gamma --> P of_type (A T)).

exists_i_query (Gamma --> (exists_i T P) of_type some A)
               (Gamma --> P of_type (A T)) :-
  print "Enter substitution term: ", read T.

and_e_tac N (Gamma --> PC of_type C)
            ((((and_e1 P) of_type A) :: (((and_e2 P) of_type B) :: Gamma1)) 
                     --> PC of_type C) :-
  nth_item_and_rest N (P of_type A and B) Gamma Gamma1.

imp_e_tac N (Gamma --> PC of_type C)
            (andgoal (Gamma1 --> PA of_type A)
                     ((((imp_e PA P) of_type B)::Gamma1) --> PC of_type C)) :-
  nth_item_and_rest N (P of_type A imp B) Gamma Gamma1.

imp_e_retain N (Gamma --> PC of_type C)
               (andgoal (Gamma --> PA of_type A)
                        ((((imp_e PA P) of_type B) :: Gamma) 
                                        --> PC of_type C)) :-
  nth_item N (P of_type A imp B) Gamma.

bchain_tac N (Gamma --> (imp_e PA P) of_type B)
             (Gamma1 --> PA of_type A) :-
  nth_item_and_rest N (P of_type A imp B) Gamma Gamma1.

fchain_tac N (Gamma --> PC of_type C)
             ((((imp_e PA P) of_type B)::Gamma2) --> PC of_type C) :-
  nth_item_and_rest N (P of_type A imp B) Gamma Gamma1,
  member_and_rest (PA of_type A) Gamma1 Gamma2.

forall_e_tac N (Gamma --> PC of_type C)
               ((((forall_e T P) of_type (A T)) :: Gamma1) --> PC of_type C) :-
  nth_item_and_rest N (P of_type forall A) Gamma Gamma1.

forall_e_query N (Gamma --> PC of_type C)
                 ((((forall_e T P) of_type (A T))::Gamma1) --> PC of_type C) :-
  print "Enter substitution term: ", read T,
  print "Remove hypothesis? ",
  (read yes, nth_item_and_rest N (P of_type forall A) Gamma Gamma1;
   Gamma1 = Gamma, nth_item N (P of_type forall A) Gamma).

or_e_tac N (Gamma --> (or_e P P1 P2) of_type C)
          (andgoal (allgoal PA\ (((PA of_type A)::Gamma1) 
                                          --> (P1 PA) of_type C))
                   (allgoal PB\ (((PB of_type B)::Gamma1) 
                                          --> (P2 PB) of_type C))) :-
  nth_item_and_rest N (P of_type A or B) Gamma Gamma1.

exists_e_tac N (Gamma --> (exists_e P PC) of_type C)
               (allgoal T\ (allgoal PA\
                 (((PA of_type (A T))::Gamma1) --> (PC T PA) of_type C))) :-
  nth_item_and_rest N (P of_type some A) Gamma Gamma1.


