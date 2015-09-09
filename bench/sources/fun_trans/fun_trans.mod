module fun_trans.

import utils.

import poly_typing.
import poly_oper_sem.
import part_eval.
import tp_part_eval.
import termination.
import trafo.
import cse.

import main.

main :- /* main1 "poly.dat",   stack overflow */
        main1 "bound_rec.dat",
        main1 "cse1.dat",
        main1 "effect2.dat",
        /* main1 "expensive1.dat",   stack overflow */
        main1 "case_elim.dat",
        main1 "effect1.dat",
        main1 "elim_pair.dat",
        main1 "part_eval1.dat". 

