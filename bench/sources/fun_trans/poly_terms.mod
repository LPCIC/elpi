module poly_terms.

accumulate terms.
accumulate poly_types.

tm_of_ptm T T :- T = u.

tm_of_ptm (pair TA1 TB1) (pair TA2 TB2) :-
  tm_of_ptm TA1 TA2,
  tm_of_ptm TB1 TB2.

tm_of_ptm (fst T1) (fst T2) :- tm_of_ptm T1 T2.
tm_of_ptm (snd T1) (snd T2) :- tm_of_ptm T1 T2.

tm_of_ptm (inl T1) (inl T2) :- tm_of_ptm T1 T2.
tm_of_ptm (inr T1) (inr T2) :- tm_of_ptm T1 T2.

tm_of_ptm (case CT1 LF1 RF1) (case CT2 LF2 RF2) :-
  tm_of_ptm CT1 CT2,
  (pi l\ tm_of_ptm (LF1 l) (LF2 l)),
  (pi r\ tm_of_ptm (RF1 r) (RF2 r)).

tm_of_ptm (lam F1) (lam F2) :- pi x\ tm_of_ptm (F1 x) (F2 x).

tm_of_ptm (rec F1) (rec F2) :- pi f\ pi x\ tm_of_ptm (F1 f x) (F2 f x).

tm_of_ptm (app TA1 TB1) (app TA2 TB2) :-
  tm_of_ptm TA1 TA2,
  tm_of_ptm TB1 TB2.

tm_of_ptm (abs_rtp T1) (abs_rtp T2) :- tm_of_ptm T1 T2.
tm_of_ptm (rep_rtp T1) (rep_rtp T2) :- tm_of_ptm T1 T2.

tm_of_ptm (tlam _ F1) (lam F2) :- pi x\ tm_of_ptm (F1 x) (F2 x).
tm_of_ptm (trec _ F1) (rec F2) :- pi f\ pi x\ tm_of_ptm (F1 f x) (F2 f x).

tm_of_ptm (tlet _ T1 F1) (app (lam F2) T2) :-
  tm_of_ptm T1 T2,
  pi x\ tm_of_ptm (F1 x) (F2 x).

tm_of_ptm (tabs TF) Res :- tm_of_ptm (TF _) Res.

tm_of_ptm T T.

tm_linear_aux (tlam _ F) A B :- tm_fun_linear_aux F A B.

tm_linear_aux (trec _ F) A B :-
  pi f\
    (pi X\ tm_linear_aux f X X) =>
      tm_fun_linear_aux (F f) A B.

tm_linear_aux (tlet _ T F) A C :-
  tm_linear_aux T A B,
  tm_fun_linear_aux F B C.

tm_linear_aux (tabs F) A B :- pi tp\ tm_linear_aux (F tp) A B.

output_ptm Ch T :- printterm Ch T.

print_ptm T :- output_ptm std_out T.
