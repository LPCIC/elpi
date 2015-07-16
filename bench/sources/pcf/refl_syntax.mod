/*
 * Code for recognizing the terms representing valid programs in the
 * simple functional programming language that is considered here
 */

module refl_syntax.

accum_sig   pcf.

type   term      tm -> o.

term (fn R) :- pi X\ ((term X) => (term (R X))).
term (M @ N) :- term M, term N.
term (fixpt R) :- pi X\((term X) => (term (R X))).
term (cond M N P) :- term M, term N, term P.

term (in X).

term and.
term or.
term false.
term truth.
term car.
term cdr.
term cons.
term nullp.
term consp.
term empty.
term equal.
term greater.
term zerop.
term minus.
term plus.
term times.

