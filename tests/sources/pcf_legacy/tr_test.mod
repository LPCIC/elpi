/*
 *  A testing harness for the code that checks for tail recursiveness
 *  of programs in the simple functional programming language.
 */

module tr_test.

accumulate tailrec, examples. 

type tr_test  string -> o.

tr_test String :- prog String T, tailrec T.
