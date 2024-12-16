/*
 * A testing harness for the general tail recursion recognizing program
 */

module  tr2_test.

accumulate  terms, general_tr. 

type  test_nb  int -> o.

test_nb 1 :- trm trfact1 F, tailrec F. 

test_nb 2 :- trm gcd2 F, tailrec F.

test_nb 3 :- trm appnd F, tailrec F.

test_nb 4 :- trm trfact2 F, tailrec F.

