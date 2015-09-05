module tp_part_eval.

accumulate utils.
accumulate tp_let_ext.
accumulate effect_monad.

% TP_PART_EVAL

tp_part_eval T1 T2 :-
  part_evalM T1 M,
  show_effM M T2.


% PART_EVALM

type part_evalM tp_astK -> effM tp_astK -> o.

part_evalM T Res :-
  T = tp_ast tp_u unit,
  unit_value_effM T Res.

part_evalM (tp_ast (tp_pair T1 T2) TP) Res :-
  part_evalM T1 M1,
  part_evalM T2 M2,
  bind_effM M1 (V1\ bind_effM M2 (simplify_pair TP V1)) Res.

part_evalM (tp_ast (tp_fst T) TP) Res :-
  part_evalM T M,
  bind_effM M (simplify_fst TP) Res.

part_evalM (tp_ast (tp_snd T) TP) Res :-
  part_evalM T M,
  bind_effM M (simplify_snd TP) Res.

part_evalM (tp_ast (tp_inl T) TP) Res :-
  part_evalM T M,
  bind_effM M (V\ unit_value_effM (tp_ast (tp_inl V) TP)) Res.

part_evalM (tp_ast (tp_inr T) TP) Res :-
  part_evalM T M,
  bind_effM M (V\ unit_value_effM (tp_ast (tp_inr V) TP)) Res.

part_evalM (tp_ast (tp_case CT LF RF) TP) Res :-
  part_evalM CT M,
  bind_effM M (CV\ simplify_case TP CV LF RF) Res.

part_evalM (tp_ast (tp_lam F1) TP) Res :-
  TP = (TP1 --> _TP2),
  tp_part_eval_fun TP1 F1 F2,
  unit_value_effM (tp_ast (tp_lam F2) TP) Res.

part_evalM (tp_ast (tp_rec F1) TP) Res :-
  TP = (TP1 --> _TP2),
  pi f\ sigma Mf\
    unit_comp_effM f Mf,
    part_evalM f Mf =>
      tp_ast_get_type f TP =>
        sigma Fx\
          tp_part_eval_fun TP1 (F1 f) Fx,
          ( % CASE: function not recursive anymore -> normal function
            unit_value_effM (tp_ast (tp_lam Fx) TP) Res
          ; % CASE: function still potentially recursive
            F2 f = Fx,
            unit_comp_effM (tp_ast (tp_rec F2) TP) Res
          ).

part_evalM (tp_ast (tp_app T1 T2) TP) Res :-
  part_evalM T1 M1,
  part_evalM T2 M2,
  bind_effM M1 (V1\ bind_effM M2 (simplify_app TP V1)) Res.

part_evalM (tp_ast (tp_abs_rtp T) TP) Res :-
  part_evalM T M,
  bind_effM M (V\ unit_value_effM (tp_ast (tp_abs_rtp V) TP)) Res.

part_evalM (tp_ast (tp_rep_rtp T) TP) Res :-
  part_evalM T M,
  bind_effM M (simplify_rep_rtp TP) Res.

part_evalM (tp_ast (tp_tlam TP1 F) TP) Res :-
  tp_part_eval_fun TP1 F1 F2,
  unit_value_effM (tp_ast (tp_tlam TP1 F2) TP) Res.

part_evalM (tp_ast (tp_trec TP1 F) TP) Res :-
  pi f\ sigma Mf\
    unit_comp_effM f Mf,
    part_evalM f Mf =>
      tp_ast_get_type f TP =>
        sigma Fx\
          tp_part_eval_fun TP1 (F1 f) Fx,
          ( % CASE: function does not contain itself anymore -> normal function
            unit_value_effM (tp_ast (tp_tlam TP1 Fx) TP) Res
          ; % CASE: function still potentially recursive
            F2 f = Fx,
            unit_comp_effM (tp_ast (tp_trec TP1 F2) TP) Res
          ).

part_evalM (tp_ast (tp_tlet S T1 F1) TP) Res :-
  part_evalM T1 MT1,
  (pi x\ sigma Mx\
    unit_value_effM x Mx,
    part_evalM x Mx =>
      (pi tp\ instantiate S tp => tp_ast_get_type x tp) =>
        sigma M\
          part_evalM (F1 x) M,
          show_effM M (F2 x)),
  bind_effM MT1 (T2\ simplify_tp_tlet TP S T2 F2) Res.

part_evalM (tp_ast (tp_tabs F1) TP) Res :-
  pi tp\
    part_evalM (F1 tp) M,
    show_effM M (F2 tp),
    unit_value_effM (tp_ast (tp_tabs F2) TP) Res.


% TP_PART_EVAL_FUN

tp_part_eval_fun TP F1 F2 :-
  pi x\ sigma Mx\
    unit_value_effM x Mx,
    part_evalM x Mx =>
      tp_ast_get_type x TP =>
        sigma M\
          part_evalM (F1 x) M,
          show_effM M (F2 x).


% SIMPLIFICATION RULES

type simplify_pair tp -> tp_astK -> tp_astK -> effM tp_astK -> o.
type simplify_fst tp -> tp_astK -> effM tp_astK -> o.
type simplify_snd tp -> tp_astK -> effM tp_astK -> o.

type simplify_case
  tp ->
  tp_astK ->
  (tp_astK -> tp_astK) ->
  (tp_astK -> tp_astK) ->
  effM tp_astK -> o.

type simplify_case_arm
  tp_astK ->
  (tp_astK -> tp_astK) ->
  (tp_astK -> tp_tm) ->
  (tp_astK -> tp_astK) -> o.

type simplify_case_arms
  tp ->
  tp_astK ->
  (tp_astK -> tp_astK) ->
  (tp_astK -> tp_astK) ->
  effM tp_astK -> o.

type simplify_app tp -> tp_astK -> tp_astK -> effM tp_astK -> o.
type simplify_term_app tp -> tp_astK -> tp_astK -> effM tp_astK -> o.

type simplify_rep_rtp tp -> tp_astK -> effM tp_astK -> o.

type simplify_tp_tlet
  tp ->
  schema -> tp_astK ->
  (tp_astK -> tp_astK) ->
  effM tp_astK -> o.


% Pair reconstructs its destructed form -> simplify.
% This is safe, because V, too, is guaranteed to be a value!
simplify_pair _TP V1 V2 Res :-
  lifted_term V1 (tp_ast (tp_fst V) _TP1),
  lifted_term V2 (tp_ast (tp_snd V) _TP2),
  !,
  unit_value_effM V Res.

simplify_pair TP V1 V2 Res :- unit_value_effM (tp_ast (tp_pair V1 V2) TP) Res.

simplify_fst _TP (tp_ast (tp_pair V1 _V2) _TPP) Res :-
  !,
  unit_value_effM V1 Res.

simplify_fst TP V Res :- unit_comp_effM (tp_ast (tp_fst V) TP) Res.

simplify_snd _TP (tp_ast (tp_pair _V1 V2) _TPP) Res :-
  !,
  unit_value_effM V2 Res.

simplify_snd TP V Res :- unit_comp_effM (tp_ast (tp_snd V) TP) Res.

simplify_case _TP (tp_ast (tp_inl V) _TPC) LF _RF Res :-
  !,
  part_evalM (LF V) Res.

simplify_case _TP (tp_ast (tp_inr V) _TPC) _LF RF Res :-
  !,
  part_evalM (RF V) Res.

% Condition not reducable to choice.
simplify_case TP CV LF1 RF1 Res :-
  tp_ast_get_type CV (TPL ++ TPR),
  tp_part_eval_fun TPL LF1 LF2,
  tp_part_eval_fun TPR RF1 RF2,
  simplify_case_arm CV LF2 tp_inl LF3,
  simplify_case_arm CV RF2 tp_inr RF3,
  simplify_case_arms TP CV LF3 RF3 Res.

% Case arm a function of condition.
simplify_case_arm CV F1 Make F2 :-
  pi x\ sigma Mx\
    unit_value_effM x Mx,
    part_evalM x Mx =>
      sigma F\ sigma M\ sigma TP\
        elim_sub_term (F1 x) (tp_ast (Make x) TP) F,
        !,
        part_evalM (F CV) M,
        show_effM M (F2 x).

% Case arm not a function of condition.
simplify_case_arm _CV F _Make F.

% Left and right case arm equivalent.
simplify_case_arms _TP CV LF RF Res :-
  pi l\ pi r\
    EQ = LF l,
    EQ = RF r,
    !,
    part_evalM EQ Res.

% Case arms not equivalent.
simplify_case_arms TP CV LF RF Res :-
  unit_comp_effM (tp_ast (tp_case CV LF RF) TP) Res.

% Application of simple lambda abstraction.
simplify_app _TP (tp_ast (tp_lam F) _TPF) V Res :- !, part_evalM (F V) Res.

% Terminating function applications.
simplify_app TP FV V Res :-
  tp_funcall_terminates FV V,
  !,
  simplify_term_app TP FV V Res.

% Maybe non-terminating function applications.
simplify_app TP FV V Res :- unit_mnont_effM (tp_ast (tp_app FV V) TP) Res.

% Terminating recursive function application.
simplify_term_app TP FV V Res :-
  FV = tp_ast (tp_rec F) _TP,
  !,
  part_evalM (F FV V) Res.

% Terminating unknown function.
simplify_term_app TP FV V Res :- unit_comp_effM (tp_ast (tp_app FV V) TP) Res.

simplify_rep_rtp _TP (tp_ast (tp_abs_rtp V) _ATP) Res :-
  !,
  unit_value_effM V Res.

simplify_rep_rtp TP V Res :- unit_comp_effM (tp_ast (tp_rep_rtp V) TP) Res.

% TODO: this is conservative - better ways (type handling may be difficult)?
simplify_tp_tlet TP S V FV Res :-
  unit_comp_effM (tp_ast (tp_tlet S V FV) TP) Res.


% SHOW_EFFM

show_effM (value_effM T) T.

show_effM EffM (tp_ast (C T G) TP2) :-
  (
    mnont_effM T F = EffM,
    C = tp_let_mnont
  ;
    comp_effM T F = EffM,
    C = tp_let_comp
  ),
  tp_ast_get_type T TP1,
  pi x\
    tp_ast_get_type x TP1 =>
      sigma Gx\
        show_effM (F x) Gx,
        tp_ast_get_type Gx TP2,
        G x = Gx.


% SPECIAL RULES FOR LIFTED TERMS

part_evalM LT Res :-
  (
    tp_ast (tp_let T F) _TP = LT
  ;
    tp_ast (tp_let_mnont T F) _TP = LT
  ;
    tp_ast (tp_let_comp T F) _TP = LT
  ),
  part_evalM T M,
  bind_effM M (V\ part_evalM (F V)) Res.

part_evalM LT Res :-
  lifted_term LT _T,
  unit_value_effM LT Res.

tp_ast_get_type LT TP :-
  lifted_term LT T,
  tp_ast_get_type T TP.
