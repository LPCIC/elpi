/*
 * A testing harness for the code in tr_recognizer that contains the 
 * definition of a predicate for recognizing tail recursiveness of 
 * two argument functions
 */

module tr1_test. 

accumulate terms, tr_recognizer. 

type test_nb  int -> o.

test_nb 1 :- trm trfact1 F, tl_rec F.

test_nb 2 :- trm gcd2 F, tl_rec F.

test_nb 3 :- trm appnd F, tl_rec F.

