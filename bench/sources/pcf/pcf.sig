/*
 * The sorts and constants needed for encoding the terms in a simple 
 * functional programming language PCF
 */

sig pcf.

kind   tm   type.

type   fn   (tm -> tm) -> tm.       % abstraction constructor

type   @    tm -> tm -> tm.         % application constructor
infixl @    6.

type fixpt (tm -> tm) -> tm.        % fixed point constructor for recursion
type cond  tm -> tm -> tm -> tm.    % conditional
type in    int -> tm.               % constructor for embedding integers

type and, or, false, truth,                      % boolean functions
     car, cdr, cons, nullp, consp, empty,        % lists functions
     equal, greater, zerop, minus, plus, times   % integer functions
     tm.

type main o.
