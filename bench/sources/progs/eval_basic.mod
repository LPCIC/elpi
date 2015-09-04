/*
 * A call-by-value evaluator for the pure lambda calculus. Observe how
 * substitution is realized simply as (Lambda Prolog) application in the 
 * second clause for eval.
 */

module eval_basic.

eval  (abs R)  (abs R).
eval  (app M N)  V  :-  eval M (abs R), eval N U, eval (R U) V.

