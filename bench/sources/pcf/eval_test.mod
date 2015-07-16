/*
 * A testing harness for the call-by-value evaluator for PCF
 */

module eval_test.

accumulate eval, examples.

type eval_test   int -> tm -> o.

eval_test 1 V :- prog "fib" Fib, eval (Fib @ in 12) V.
eval_test 2 V :- prog "map" Map, prog "fib" Fib, 
             eval (Map @ Fib @ (cons @ in 3 @ (cons @ in 6 @ empty))) V.
eval_test 3 V :- prog "app" App, 
             eval (App @ (cons @ in 3 @ empty) @ (cons @ in 5 @ empty)) V.
eval_test 4 V :- prog "mem" Mem, 
             eval (Mem @ (in 3) @ (cons @ in 5 @ (cons @ in 3 @ empty))) V.
eval_test 5 V :- prog "mem" Mem, 
             eval (Mem @ (in 4) @ (cons @ in 5 @ (cons @ in 3 @ empty))) V.


