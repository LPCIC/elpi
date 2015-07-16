/*
 * Illustration of encodings of programs in the simple functional 
 * programming language
 */

module examples.

type prog    string -> tm -> o.

prog "successor" 
  (fn x\ plus @ x @ (in 1)).

prog "onep" 
  (fn w\ fn u\ fn v\ cond (equal @ (in 1) @ w) u v).

prog "is_sym"
  (fn f\ fn x\ fn y\ equal @ (f @ x @ y) @ (f @ y @ x)).

prog "fib" 
  (fixpt fib\ fn n\ cond (zerop @ n) (in 0) 
                     (cond (equal @ n @ (in 1)) (in 1) 
                           (plus @ (fib @ (minus @ n @ (in 1))) @ 
                                   (fib @ (minus @ n @ (in 2)))))).

prog "map" 
  (fixpt map\ fn f\ fn l\ 
     cond (nullp @ l) empty 
          (cons @ (f @ (car @ l)) @ (map @ f @ (cdr @ l)))).

prog "mem" 
  (fixpt mem\ fn x\ fn l\ 
    cond (nullp @ l) false 
         (cond (and @ (consp @ l) @ (equal @ (car @ l) @ x)) 
                truth (mem @ x @ (cdr @ l)))).

prog "fact" 
  (fixpt f\ fn n\ fn m\
    cond (equal @ n @ (in 0)) m
         (f @ (minus @ n @ (in 1)) @ (times @ n @ m))).

prog "app"
  (fixpt app\ fn l\ fn k\
    (cond (nullp @ l) k (cons @ (car @ l) @ (app @ (cdr @ l) @ k)))).

prog "gcd" 
  (fixpt f\ fn x\ fn y\ 
    cond (equal @ (in 1) @ x) (in 1)
         (cond (greater @ y @ x) (f @ y @ x)
               (cond (equal @ x @ y) x (f @ (minus @ x @ y) @ y)))).

prog "ex1"   (cons @ (in 1) @ (in 2)).
prog "ex2"   (plus @ empty @ (in 1)).
prog "ex3"   (cond truth (in 3) empty).
prog "ex4"   (fn x\ fn x\x).
prog "ex5"   (cond truth (in 3) (in 5)).
prog "ex6"   ((fn x\x) @ (fn y\y)).
prog "i"     (fn x\ x).
prog "k"     (fn x\ fn y\x).
prog "s"     (fn x\ fn y\ fn z\ (x @ z) @ (y @ z)).
prog "comp"  (fn f\ fn g\ fn x\ f @ (g @ x)).

