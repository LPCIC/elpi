/*
 *  A testing harness for the code that infers polytypes for programs
 *  in the simple functional programming language.
 */

module poly_test.

accumulate polyinfer, examples. 

type poly_test  string -> poly -> o.

poly_test String Ty :- prog String T, polyinfer T Ty.
