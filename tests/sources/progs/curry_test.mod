/*
 * A harness for testing the code implementing the `currying' transform
 */

module  curry_test. 

accumulate terms, curry_transform. 

type test int -> tm -> o.

test 1 CurriedF :- trm trfact2 F, curry F CurriedF.
