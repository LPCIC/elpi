module typing.

accumulate terms.
accumulate types.

infer_tp u unit.

infer_tp (pair T1 T2) (TP1 ** TP2) :-
  infer_tp T1 TP1,
  infer_tp T2 TP2.

infer_tp (fst T) TP1 :- infer_tp T (TP1 ** _TP2).
infer_tp (snd T) TP2 :- infer_tp T (_TP1 ** TP2).

infer_tp (inl T) (TP1 ++ _TP2) :- infer_tp T TP1.
infer_tp (inr T) (_TP1 ++ TP2) :- infer_tp T TP2.

infer_tp (case CT LF RF) TP :-
  infer_tp CT (TP1 ++ TP2),
  (pi l\ infer_tp l TP1 => infer_tp (LF l) TP),
  (pi r\ infer_tp r TP2 => infer_tp (RF r) TP).

infer_tp (lam F) (TP1 --> TP2) :- pi x\ infer_tp x TP1 => infer_tp (F x) TP2.

infer_tp (rec F) TP :-
  TP = (TP1 --> TP2),
  pi f\ pi x\
    infer_tp f TP =>
      infer_tp x TP1 => infer_tp (F f x) TP2.

infer_tp (app T1 T2) TP2 :-
  infer_tp T1 (TP1 --> TP2),
  infer_tp T2 TP1.

infer_tp (abs_rtp T) TP :-
  TP = mu TF,
  infer_tp T (TF TP).

infer_tp (rep_rtp T) (TF TP) :-
  TP = mu TF,
  infer_tp T TP.
