/*
 * A call-by-value interpreter for PCF
 */

module eval.

accumulate control.       % for control predicates used in the code

type eval          tm -> tm -> o.
type apply         tm -> tm -> tm -> o.
type special       tm -> int -> list tm -> tm.
type eval_special  tm -> list tm -> tm -> o.

eval (fn M)   (fn M).
eval (M @ N)   V :- eval M Fun, eval N U, apply Fun U V.
eval (fixpt R) V :- eval (R (fixpt R)) V.
eval (cond Cond Then Else) V :- 
  eval Cond Bool, if (Bool = truth) (eval Then V) (eval Else V).
eval (in N)    (in N).
eval truth     truth.
eval false     false.
eval empty     empty.

% The value of the special built-in functions is given as a 
% special construction: it contains the arity and the arguments 
% already supplied (which starts out as empty).

eval and     (special and     2 nil).
eval car     (special car     1 nil).
eval cdr     (special cdr     1 nil).
eval cons    (special cons    2 nil).
eval consp   (special consp   1 nil).
eval equal   (special equal   2 nil).
eval greater (special greater 2 nil).
eval minus   (special minus   2 nil).
eval nullp   (special nullp   1 nil).
eval plus    (special plus    2 nil).
eval times   (special times   2 nil).
eval zerop   (special zerop   1 nil).

% apply describes how to apply a fnbda abstract or a special to
% arguments.

apply (fn R) U V :- eval (R U) V.
apply (special Fun 1 Args) U V :- !, eval_special Fun (U::Args) V.
apply (special Fun C Args) U (special Fun K (U::Args)) :- K is C - 1.

% Links between the built-in functions and their actual meaning
% is given in the following lines.

%% List primitives

eval_special car   ((cons @ V @ U)::nil) V.
eval_special cdr   ((cons @ V @ U)::nil) U.
eval_special cons  (U::V::nil) (cons @ V @ U).
eval_special nullp (U::nil) V :- if (U = empty) (V = truth) (V = false).
eval_special consp (U::nil) V :- if (U = empty) (V = false) (V = truth).

% Boolean primitives
eval_special and (B2::B1::nil) V :-
  if (B1 = false) (V = false) (if (B2 = false) (V = false) (V = truth)).
eval_special or  (B2::B1::nil) V :-
  if (B1 = truth) (V = truth) (if (B2 = truth) (V = truth) (V = false)).

% Integer primitives
eval_special minus ((in N)::(in M)::nil) (in V) :- V is M - N.
eval_special plus  ((in N)::(in M)::nil) (in V) :- V is M + N.
eval_special times ((in N)::(in M)::nil) (in V) :- V is M * N.
eval_special zerop ((in N)::nil) V :- if (N = 0) (V = truth) (V = false).
eval_special equal (B2::B1::nil) V :- if (B1 = B2) (V = truth) (V = false).
eval_special greater ((in N)::(in M)::nil) V :- 
  if (M > N) (V = truth) (V = false).
