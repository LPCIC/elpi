module let_ext.

accumulate oper_sem.

type inln_let (tm -> (tm -> tm) -> tm -> o) -> tm -> tm -> o.
type inln_fun (tm -> (tm -> tm) -> tm -> o) -> (tm -> tm) -> (tm -> tm) -> o.

type maybe_inln_linear
  (tm -> (tm -> tm) -> tm -> o) -> tm -> (tm -> tm) -> tm -> o.

unsafe_inline_let T1 T2 :- inln_let (T\F\Res\ Res = let T F) T1 T2.
unsafe_let_to_app T1 T2 :- inln_let (T\F\Res\ Res = app (lam F) T) T1 T2.

inln_let _P T T :- T = u.

inln_let P (pair TA1 TB1) (pair TA2 TB2) :-
  inln_let P TA1 TA2,
  inln_let P TB1 TB2.

inln_let P (fst T1) (fst T2) :- inln_let P T1 T2.
inln_let P (snd T1) (snd T2) :- inln_let P T1 T2.

inln_let P (inl T1) (inl T2) :- inln_let P T1 T2.
inln_let P (inr T1) (inr T2) :- inln_let P T1 T2.

inln_let P (case CT1 LF1 RF1) (case CT2 LF2 RF2) :-
  inln_let P CT1 CT2,
  inln_fun P LF1 LF2,
  inln_fun P RF1 RF2.

inln_let P (lam F1) (lam F2) :- inln_fun P F1 F2.

inln_let P (rec F1) (rec F2) :-
  pi f\
    inln_let P f f =>
      (pi X\ tm_linear_aux f X X) =>
        inln_fun P (F1 f) (F2 f).

inln_let P (app TA1 TB1) (app TA2 TB2) :-
  inln_let P TA1 TA2,
  inln_let P TB1 TB2.

inln_let P (abs_rtp T1) (abs_rtp T2) :- inln_let P T1 T2.
inln_let P (rep_rtp T1) (rep_rtp T2) :- inln_let P T1 T2.

inln_let P (let_mnont T F1) Res :-
  inln_fun P F1 F2,
  P T F2 Res.

inln_let P (let_comp T F) Res :- maybe_inln_linear P T F Res.

inln_fun P F1 F2 :-
  pi x\
    inln_let P x x =>
      (pi X\ tm_linear_aux x X X) =>
        inln_let P (F1 x) (F2 x).

maybe_inln_linear P T F Res :-
  tm_fun_linear F,
  !,
  inln_let P (F T) Res.

maybe_inln_linear P T F1 Res :-
  (pi t\ inln_let P t t => inln_let P (F1 t) (F2 t)),
  P T F2 Res.

tm_linear_aux LT A C :-
  (
    let T F = LT
  ;
    let_mnont T F = LT
  ;
    let_comp T F = LT
  ),
  tm_linear_aux T A B,
  pi x\
    (pi X\ tm_linear_aux x X X) =>
      tm_linear_aux (F x) B C.

eval LT Res :-
  (
    let T1 F = LT
  ;
    let_mnont T1 F = LT
  ;
    let_comp T1 F = LT
  ),
  eval T1 T2,
  eval (F T2) Res.
