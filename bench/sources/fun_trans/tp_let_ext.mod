module tp_let_ext.

accumulate tp_terms.

type inln_let
  (tp_astK -> (tp_astK -> tp_astK) -> tp_astK -> o) ->
  tp_astK -> tp_astK -> o.

type inln_fun
  (tp_astK -> (tp_astK -> tp_astK) -> tp_astK -> o) ->
  (tp_astK -> tp_astK) -> (tp_astK -> tp_astK) -> o.

type maybe_inln_linear
  (tp_astK -> (tp_astK -> tp_astK) -> tp_astK -> o) ->
  tp_astK -> (tp_astK -> tp_astK) -> tp_astK -> o.

unsafe_inline_tp_let T1 T2 :-
  inln_let (T\F\Res\
    (pi x\ tp_ast_get_type (F x) TP),
    Res = tp_ast (tp_let T F) TP) T1 T2.

unsafe_tp_let_to_app T1 T2 :-
  inln_let (T\F\Res\
    tp_ast_get_type T TP1,
    (pi x\ tp_ast_get_type (F x) TP2),
    Res = tp_ast (tp_app (tp_ast (tp_lam F) (TP1 --> TP2)) T) TP2) T1 T2.

inln_let _P T T :- T = tp_ast tp_u unit.

inln_let P (tp_ast (tp_pair TA1 TB1) TP) (tp_ast (tp_pair TA2 TB2) TP) :-
  inln_let P TA1 TA2,
  inln_let P TB1 TB2.

inln_let P (tp_ast (tp_fst T1) TP) (tp_ast (tp_fst T2) TP) :- inln_let P T1 T2.
inln_let P (tp_ast (tp_snd T1) TP) (tp_ast (tp_snd T2) TP) :- inln_let P T1 T2.

inln_let P (tp_ast (tp_inl T1) TP) (tp_ast (tp_inl T2) TP) :- inln_let P T1 T2.
inln_let P (tp_ast (tp_inr T1) TP) (tp_ast (tp_inr T2) TP) :- inln_let P T1 T2.

inln_let P (tp_ast (tp_case CT1 LF1 RF1) TP)
           (tp_ast (tp_case CT2 LF2 RF2) TP) :-
  inln_let P CT1 CT2,
  inln_fun P LF1 LF2,
  inln_fun P RF1 RF2.

inln_let P (tp_ast (tp_lam F1) TP) (tp_ast (tp_lam F2) TP) :- inln_fun P F1 F2.

inln_let P (tp_ast (tp_rec F1) TP) (tp_ast (tp_rec F2) TP) :-
  pi f\
    inln_let P f f =>
      (pi X\ tp_tm_linear_aux f X X) =>
        inln_fun P (F1 f) (F2 f).

inln_let P (tp_ast (tp_app TA1 TB1) TP) (tp_ast (tp_app TA2 TB2) TP) :-
  inln_let P TA1 TA2,
  inln_let P TB1 TB2.

inln_let P (tp_ast (tp_abs_rtp T1) TP) (tp_ast (tp_abs_rtp T2) TP) :-
  inln_let P T1 T2.

inln_let P (tp_ast (tp_rep_rtp T1) TP) (tp_ast (tp_rep_rtp T2) TP) :-
  inln_let P T1 T2.

inln_let P (tp_ast (tp_tlam TP1 F1) TP) (tp_ast (tp_tlam TP1 F2) TP) :-
  inln_fun P F1 F2.

inln_let P (tp_ast (tp_trec TP1 F1) TP) (tp_ast (tp_trec TP1 F2) TP) :-
  pi f\
    inln_let P f f =>
      (pi X\ tp_tm_linear_aux f X X) =>
        inln_fun P (F1 f) (F2 f).

% TODO: this is conservative - better ways (type handling may be difficult)?
inln_let P (tp_ast (tp_tlet S T1 F1) TP) (tp_ast (tp_tlet S T2 F2) TP) :-
  inln_let P T1 T2,
  inln_fun P F1 F2.

inln_let P (tp_ast (tp_tabs F1) TP) (tp_ast (tp_tabs F2) TP) :-
  pi tp\ inln_let P (F1 tp) (F2 tp).

inln_let P (tp_ast (tp_let_mnont T F1) TP) Res :-
  inln_fun P F1 F2,
  P T F2 Res.

inln_let P (tp_ast (tp_let_comp T F) _TP) Res :- maybe_inln_linear P T F Res.

inln_fun P F1 F2 :-
  pi x\
    inln_let P x x =>
      (pi X\ tp_tm_linear_aux x X X) =>
        inln_let P (F1 x) (F2 x).

maybe_inln_linear P T F Res :-
  tp_tm_fun_linear F1,
  !,
  inln_let P (F T) Res.

maybe_inln_linear P T F1 Res :-
  (pi t\ inln_let P t t => inln_let P (F1 t) (F2 t)),
  P T F2 Res.

tp_tm_linear_aux LT A C :-
  (
    tp_ast (tp_let T F) _ = LT
  ;
    tp_ast (tp_let_mnont T F) _ = LT
  ;
    tp_ast (tp_let_comp T F) _ = LT
  ),
  tp_tm_linear_aux T A B,
  pi x\
    (pi X\ tp_tm_linear_aux x X X) =>
      tp_tm_linear_aux (F x) B C.
