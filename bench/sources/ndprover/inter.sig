/*
 * Interface to an implementation of an interactive theorem prover.
 */

sig  inter.

accum_sig  logic, nonlogical, formulas, ndproofs, ndtac, tacticals.

exportdef   inter_top	        name -> proof_object -> goal -> o.
exportdef   inter	        goal -> goal -> o.
exportdef   do                  o -> goal -> goal -> o.
exportdef   quitg	        goal -> goal -> o.
exportdef   backup              goal -> goal -> o.
exportdef   print_form_list	list judgment -> int -> o.
exportdef   nl                  o.
exportdef   write               A -> o.
