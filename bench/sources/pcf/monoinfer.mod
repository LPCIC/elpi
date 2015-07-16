/*
 * Code for inferring monotypes for programs in the simple 
 * functional programming language
 */

module monoinfer.

accum_sig  pcf, monotypes.

type prim, infer      tm -> ty -> o.

infer (M @ N) B        :- infer M (A --> B), infer N A.
infer (fn M) (A --> B) :- pi x\ infer x A => infer (M x) B.
infer (fixpt M) A      :- pi x\ infer x A => infer (M x) A.
infer (cond C T E) A   :- infer C bool, infer T A, infer E A.
infer T A              :- prim T A.

% Primitive for lists.

prim car    ((lst A) --> A).
prim cdr    ((lst A) --> (lst A) ).
prim empty  (lst A).
prim cons   (A --> (lst A) --> (lst A) ).
prim nullp  ((lst A) --> bool).
prim consp  ((lst A) --> bool).

% Primitives for booleans.

prim equal  (A --> A --> bool).
prim and    (bool --> bool --> bool).
prim or     (bool --> bool --> bool).
prim truth   bool.
prim false   bool.

% Primitives for integers

prim times    (num --> num --> num).
prim plus     (num --> num --> num).
prim minus    (num --> num --> num).
prim zerop    (num --> bool).
prim greater  (num --> num --> bool).
prim (in N)    num.
