/*
 * Code for inferring polytypes for programs in the simple functional
 * programming language
 */

module polyinfer.

accum_sig  polytypes, pcf, unifytypes.

accumulate  unifytypes.

% Predicate for distinguishing constants representing type variables
type   tvar    ty -> o.


% Variable representing the initial type of a term
type   topvar  ty.

tvar topvar.


% Predicate for removing vacuous quantifications in poly types.
type  rem_vac   poly -> poly -> o.

rem_vac (c Ty) (c Ty).
rem_vac (all x\P) Q     :- !, rem_vac P Q.
rem_vac (all P) (all Q) :- pi x\ rem_vac (P x) (Q x).


% Polytypes of primitives in the programming language
type prim_poly    tm -> poly -> o.

prim_poly car      (all A\ c ((lst A) --> A)).
prim_poly cdr      (all A\ c ((lst A) --> (lst A))).
prim_poly empty    (all A\ c (lst A)).
prim_poly cons     (all A\ c (A --> (lst A) --> (lst A))).
prim_poly nullp    (all A\ c ((lst A) --> bool)).
prim_poly consp    (all A\ c ((lst A) --> bool)).
  
prim_poly equal    (all A\ c (A --> A --> bool)).
prim_poly and      (c (bool --> bool --> bool)).
prim_poly or       (c (bool --> bool --> bool)).
prim_poly truth    (c bool).
prim_poly false    (c bool).

prim_poly times    (c (num --> num --> num)).
prim_poly plus     (c (num --> num --> num)).
prim_poly minus    (c (num --> num --> num)).
prim_poly zerop    (c (num --> bool)).
prim_poly greater  (c (num --> num --> bool)).
prim_poly (in N)   (c  num).


% Representing typing judgements; these are essentially term, type pairs
kind pair    type -> type -> type.     
type pr      A -> B -> pair A B.


% Inferring a poly type for a term. The main work is done in typeof that
% generates typing judgements and constraints between these, and invokes
% type unification to solve the constraints.
type  tybind      tm -> ty -> o.
type  tyinfer     tm -> poly -> o.
type  typeof      list (pair tm ty) -> list eq -> poly -> o.
type  poly_inst   poly -> ty -> list (pair tm ty) -> list eq -> poly -> o.

tyinfer Term Poly :- typeof (pr Term topvar :: nil) nil Poly.

typeof (pr (M @ N) A ::S) Eqs (all P) :- !,
  pi c\ tvar c => typeof (pr M (c --> A) :: pr N c :: S) Eqs (P c). 

typeof (pr (fn M) A :: S) Eqs  (all d\ all e\ P d e) :- !,
  pi d\ tvar d => pi e\ tvar e => pi x\ tybind x d => 
   typeof (pr (M x) e :: S) ((A == d --> e) :: Eqs) (P d e).

typeof (pr (fixpt M) A :: S) Eqs  (all P) :- !,
  pi d\ tvar d => pi x\ tybind x d => 
   typeof (pr (M x) d :: S) ((A == d) :: Eqs) (P d).

typeof (pr (cond Cond Then Else) A :: S) Eqs P :- !, 
  typeof (pr Cond bool :: pr Then A :: pr Else A :: S) Eqs P.

typeof (pr C B :: S) Eqs Poly :-
  prim_poly C Ty, !, poly_inst Ty B S Eqs Poly.

typeof (pr X B :: S) Eqs Poly :-
  tybind X A, typeof S ((A == B) :: Eqs) Poly.

typeof nil Eqs (c Ty) :-  unify Eqs topvar Ty.

poly_inst (c Ty)    B S Eqs Poly :- typeof S ((Ty == B) :: Eqs) Poly.
poly_inst (all Ty) B S Eqs (all Poly) :- 
    pi x\ tvar x => poly_inst (Ty x) B S Eqs (Poly x).


% The main predicate. Infer a poly type first and then prune 
% vacuous quantifications
type  polyinfer  tm -> poly -> o.

polyinfer Tm Ty :- tyinfer Tm PreTy, rem_vac PreTy Ty.
