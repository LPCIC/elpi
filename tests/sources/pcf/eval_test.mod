/*
 * A testing harness for the call-by-value evaluator for PCF
 */

module eval_test.

accumulate eval, examples.

type eval_test   int -> tm -> o.

eval_test 1 V :- prog "fib" Fib, eval (Fib # embed 12) V.
eval_test 2 V :- prog "map" Map, prog "fib" Fib, 
             eval (Map # Fib # (lcons # embed 3 # (lcons # embed 6 # empty))) V.
eval_test 3 V :- prog "app" App, 
             eval (App # (lcons # embed 3 # empty) # (lcons # embed 5 # empty)) V.
eval_test 4 V :- prog "mem" Mem, 
             eval (Mem # (embed 3) # (lcons # embed 5 # (lcons # embed 3 # empty))) V.
eval_test 5 V :- prog "mem" Mem, 
             eval (Mem # (embed 4) # (lcons # embed 5 # (lcons # embed 3 # empty))) V.


