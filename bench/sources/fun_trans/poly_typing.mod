module poly_typing.

accumulate typing.
accumulate poly_terms.
accumulate poly_types.

subsumes S S.
subsumes S1 (all S2) :- pi tp\ subsumes S1 (S2 tp).
subsumes (all S1) S2 :- subsumes (S1 T) S2.

generalize (all S) (tabs TF) :- pi t\ generalize (S t) (TF t).
generalize (in TP) T :- infer_tp T TP.

instantiate (all SF) T1 :- instantiate (SF _T2) T1.
instantiate (in TP) TP.

infer_tp (tlam TP1 F) (TP1 --> TP2) :-
  pi x\ infer_tp x TP1 => infer_tp (F x) TP2.

infer_tp (trec TP1 F) TP :-
  TP = (TP1 --> TP2),
  pi f\ pi x\
    infer_tp f TP =>
      infer_tp x TP1 => infer_tp (F f x) TP2.

infer_tp (tlet S T F) TP :-
  generalize S T,
  pi x\
    (pi tp\ instantiate S tp => infer_tp x tp) =>
      infer_tp (F x) TP.

infer_tp (tabs F) TP :- pi x\ infer_tp x TP1 => infer_tp (F TP1) TP.
