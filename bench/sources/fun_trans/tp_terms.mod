module tp_terms.

accumulate poly_typing.

tp_ast_get_term (tp_ast U _TP) U.

tp_ast_get_type (tp_ast _U TP) TP.

make_tp_ast u (tp_ast tp_u unit).

make_tp_ast (pair T1 T2) (tp_ast (tp_pair U1 U2) (TP1 ** TP2)) :-
  make_tp_ast T1 U1,
  tp_ast_get_type U1 TP1,
  make_tp_ast T2 U2,
  tp_ast_get_type U2 TP2.

make_tp_ast (fst T) (tp_ast (tp_fst U) TP1) :-
  make_tp_ast T U,
  tp_ast_get_type U (TP1 ** _TP2).

make_tp_ast (snd T) (tp_ast (tp_snd U) TP2) :-
  make_tp_ast T U,
  tp_ast_get_type U (_TP1 ** TP2).

make_tp_ast (inl T) (tp_ast (tp_inl U) (TP1 ++ _TP2)) :-
  make_tp_ast T U,
  tp_ast_get_type U TP1.

make_tp_ast (inr T) (tp_ast (tp_inr U) (_TP1 ++ TP2)) :-
  make_tp_ast T U,
  tp_ast_get_type U TP2.

make_tp_ast (case CT LF RF) (tp_ast (tp_case UC ULF URF) TP3) :-
  make_tp_ast CT UC,
  tp_ast_get_type UC (TP1 ++ TP2),
  conv_fun LF ULF (TP1 --> TP3),
  conv_fun RF URF (TP2 --> TP3).

make_tp_ast (lam F) (tp_ast (tp_lam UF) TP) :- conv_fun F UF TP.

make_tp_ast (rec F) (tp_ast (tp_rec UF) TP) :- conv_rec F UF TP.

make_tp_ast (app T1 T2) (tp_ast (tp_app U1 U2) TP2) :-
  make_tp_ast T1 U1,
  tp_ast_get_type U1 (TP1 --> TP2),
  make_tp_ast T2 U2,
  tp_ast_get_type U2 TP1.

make_tp_ast (abs_rtp T) (tp_ast (tp_abs_rtp U) TP) :-
  make_tp_ast T U,
  TP = mu TF,
  tp_ast_get_type U (TF TP).

make_tp_ast (rep_rtp T) (tp_ast (tp_rep_rtp U) (TF TP)) :-
  make_tp_ast T U,
  TP = mu TF,
  tp_ast_get_type U TP.

make_tp_ast (tlam TP1 F) (tp_ast (tp_tlam TP1 UF) TP) :-
  TP = (TP1 --> TP2),
  conv_fun F UF TP.

make_tp_ast (trec TP1 F) (tp_ast (tp_trec TP1 UF) TP) :-
  TP = (TP1 --> _TP2),
  conv_rec F UF TP.

make_tp_ast (tlet S T F) (tp_ast (tp_tlet S U UF) TP) :-
  generalize S T,
  make_tp_ast T U,
  pi x\ pi tp_x\
    make_tp_ast x tp_x =>
      (pi tp\ instantiate S tp => tp_ast_get_type tp_x tp) =>
        sigma Ux\
          make_tp_ast (F x) Ux,
          tp_ast_get_type Ux TP,
          UF tp_x = Ux.

make_tp_ast (tabs F) (tp_ast (tp_tabs UF) TP) :-
  pi x\ pi tp_x\
    make_tp_ast x tp_x =>
      tp_ast_get_type tp_x TP1 =>
        make_tp_ast (F TP1) U,
        tp_ast_get_type U TP,
        UF TP1 = U.


% CONV_FUN

type conv_fun (tm -> tm) -> (tp_astK -> tp_astK) -> tp -> o.

conv_fun F UF TP :-
  TP = (TP1 --> TP2),
  pi x\ pi tp_x\
    make_tp_ast x tp_x =>
      tp_ast_get_type tp_x TP1 =>
        sigma U\
          make_tp_ast (F x) U,
          tp_ast_get_type U TP2,
          UF tp_x = U.


% CONV_REC

type conv_rec (tm -> tm -> tm) -> (tp_astK -> tp_astK -> tp_astK) -> tp -> o.

conv_rec F UF TP :-
  pi f\ pi tp_f\
    make_tp_ast f tp_f =>
      tp_ast_get_type tp_f TP =>
        conv_fun (F f) (UF tp_f) TP.


% TP_TM_FUN_LINEAR

tp_tm_fun_linear F :-
  pi v\
    tp_tm_linear_aux v true fail =>
      tp_tm_linear_aux (F v) true _.

tp_tm_linear_aux (tp_ast tp_u _) X X.

tp_tm_linear_aux (tp_ast (tp_pair T1 T2) _) A C :-
  tp_tm_linear_aux T1 A B,
  tp_tm_linear_aux T2 B C.

tp_tm_linear_aux (tp_ast (tp_fst T) _) A B :- tp_tm_linear_aux T A B.
tp_tm_linear_aux (tp_ast (tp_snd T) _) A B :- tp_tm_linear_aux T A B.

tp_tm_linear_aux (tp_ast (tp_inl T) _) A B :- tp_tm_linear_aux T A B.
tp_tm_linear_aux (tp_ast (tp_inr T) _) A B :- tp_tm_linear_aux T A B.

tp_tm_linear_aux (tp_ast (tp_case CT LF RF) _) A C :-
  tp_tm_linear_aux CT A B,
  tp_tm_fun_linear_aux LF B C1,
  tp_tm_fun_linear_aux RF B C2,
  (
    C1,
    C = C2
  ;
    C = fail
  ).

tp_tm_linear_aux (tp_ast (tp_lam F) _) A B :- tp_tm_fun_linear_aux F A B.

tp_tm_linear_aux (tp_ast (tp_rec F) _) A B :-
  pi f\
    (pi X\ tp_tm_linear_aux f X X) =>
      tp_tm_fun_linear_aux (F f) A B.

tp_tm_linear_aux (tp_ast (tp_app T1 T2) _) A C :-
  tp_tm_linear_aux T1 A B,
  tp_tm_linear_aux T2 B C.

tp_tm_linear_aux (tp_ast (tp_abs_rtp T) _) A B :- tp_tm_linear_aux T A B.
tp_tm_linear_aux (tp_ast (tp_rep_rtp T) _) A B :- tp_tm_linear_aux T A B.

tp_tm_linear_aux (tp_ast (tp_tlam _ F) _) A B :- tp_tm_fun_linear_aux F A B.

tp_tm_linear_aux (tp_ast (tp_trec _ F) _) A B :-
  pi f\
    (pi X\ tp_tm_linear_aux f X X) =>
      tp_tm_fun_linear_aux (F f) A B.

tp_tm_linear_aux (tp_ast (tp_tlet _ T F) _) A C :-
  tp_tm_linear_aux T A B,
  tp_tm_fun_linear_aux F B C.

tp_tm_linear_aux (tp_ast (tp_tabs F) _) A B :-
  pi tp\ tp_tm_linear_aux (F tp) A B.

tp_tm_fun_linear_aux F A B :-
  pi x\
    (pi X\ tp_tm_linear_aux x X X) =>
      tp_tm_linear_aux (F x) A B.

output_tp_ast Ch T :- printterm Ch T.

print_tp_ast T :- output_tp_ast std_out T.
