/*
 * Code for recognizing the terms representing valid programs in the
 * simple functional programming language that is considered here
 */

module refl_syntax.

type   term      tm -> o.

term (abs R) :- pi X\ ((term X) => (term (R X))).
term (app M N) :- term M, term N.
term (cond M N P) :- term M, term N, term P.
term (fix R) :- pi X\((term X) => (term (R X))).

term truth.
term false.
term (c X).
term null.
term (cons Hd Tl) :- term Hd, term Tl.

term (&& M N) :- term M, term N.
term (plus M N) :- term M, term N.
term (minus M N) :- term M, term N.
term (times M N) :- term M, term N.
term (lss M N) :- term M, term N.
term (eq M N)  :- term M, term N.
term (intp M) :- term M.
term (pr M N) :- term M, term N.
term (prp M) :- term M.
term (fst M) :- term M.
term (snd M) :- term M.
term (nullp L) :- term L.
term (hd L) :- term L.
term (tl L) :- term L. 
term err.
