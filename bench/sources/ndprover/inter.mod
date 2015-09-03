/*
 * Implementation of an interactive theorem prover based on the use of
 * tactics and tacticals. This is the main program in this directory.
 */

module inter.

accum_sig  logic, nonlogical, formulas, ndproofs, ndtac, tacticals.

accumulate ndtac, tacticals, formulas.

type	inter_top	name -> proof_object -> goal -> o.
type	inter		goal -> goal -> o.
type	do		o -> goal -> goal -> o.
type	quitg		goal -> goal -> o.
type	backup		goal -> goal -> o.
type	print_form_list	list judgment -> int -> o.
type    nl              o.
type    write           A -> o.
type    process_input   (goal -> goal -> o) -> goal -> goal -> o.

inter_top Name P OutGoal :- formula Name Formula,
  inter (nil --> P of_type Formula) OutGoal.


inter (Gamma --> P of_type A) NewGoal :-
  nl, print "Assumptions: ",
  nl, print_form_list Gamma 1,
  nl, print "Conclusion: ",
  nl, write A, nl,
  print "Enter tactic: ", read Tac,
  process_input Tac (Gamma --> P of_type A) NewGoal.

process_input backup _ _ :- !, fail.
process_input quitg NewGoal NewGoal :- !.
process_input (do G) OldGoal NewGoal :- G, inter OldGoal NewGoal.
process_input Tac OldGoal NewGoal :-
  Tac OldGoal MidGoal, maptac inter MidGoal NewGoal.
process_input _ OldGoal NewGoal :- 
  inter OldGoal NewGoal. 

print_form_list nil N.
print_form_list ((P of_type A)::Tail) N :-
  write N, print " ", write A, nl,
  (N1 is (N + 1)),
  print_form_list Tail N1.

write A :- term_to_string A Str, print Str.
nl :- print "\n".
