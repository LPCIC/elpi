module cse.

type elim_cse_aux tm -> tm -> o.
type elim_comp tm -> (tm -> tm) -> tm -> o.
type eliminated tm -> tm -> o.

elim_cse T1 T2 :- elim_cse_aux T1 T2, !.
elim_cse T T.

elim_cse_aux T T :- T = u.
elim_cse_aux (pair TA1 TB1) (pair TA2 TB2) :-
  elim_cse TA1 TA2,
  elim_cse TB1 TB2.

elim_cse_aux (fst T1) (fst T2) :- elim_cse T1 T2.
elim_cse_aux (snd T1) (snd T2) :- elim_cse T1 T2.

elim_cse_aux (inl T1) (inl T2) :- elim_cse T1 T2.
elim_cse_aux (inr T1) (inr T2) :- elim_cse T1 T2.

elim_cse_aux (case CT1 LF1 RF1) (case CT2 LF2 RF2) :-
  elim_cse CT1 CT2,
  (pi l\ elim_cse (LF1 l) (LF2 l)),
  (pi r\ elim_cse (RF1 r) (RF2 r)).

elim_cse_aux (lam F1) (lam F2) :-
  (pi x\ elim_cse (F1 x) (F2 x)).

elim_cse_aux (rec F1) (rec F2) :-
  (pi f\ pi x\ elim_cse (F1 f x) (F2 f x)).

elim_cse_aux (app TA1 TB1) (app TA2 TB2) :-
  elim_cse TA1 TA2,
  elim_cse TB1 TB2.

elim_cse_aux (abs_rtp T1) (abs_rtp T2) :- elim_cse T1 T2.
elim_cse_aux (rep_rtp T1) (rep_rtp T2) :- elim_cse T1 T2.

elim_cse_aux (let T1 F1) (let T2 F2) :-
  elim_cse T1 T2,
  (pi x\ elim_cse (F1 x) (F2 x)).

elim_cse_aux (let_mnont T1 F1) (let_mnont T2 F2) :-
  elim_cse T1 T2,
  (pi x\ elim_cse (F1 x) (F2 x)).

elim_cse_aux (let_comp T F) Res :- elim_comp T F Res.

elim_comp T1 F Res :-
  eliminated T1 T2,
  !,
  elim_cse (F T2) Res.

elim_comp T F1 (let_comp T F2) :-
  pi x\ eliminated T x => elim_cse (F1 x) (F2 x).
