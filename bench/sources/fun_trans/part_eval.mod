module part_eval.

accumulate utils.
accumulate let_ext.
accumulate effect_monad.

% PART_EVAL

part_eval T1 T2 :-
  part_evalM T1 M,
  show_effM M T2.


% PART_EVALM

type part_evalM tm -> effM tm -> o.

part_evalM T Res :-
  T = u,
  unit_value_effM T Res.

part_evalM (pair T1 T2) Res :-
  part_evalM T1 M1,
  part_evalM T2 M2,
  bind_effM M1 (V1\ bind_effM M2 (simplify_pair V1)) Res.

part_evalM (fst T) Res :-
  part_evalM T M,
  bind_effM M simplify_fst Res.

part_evalM (snd T) Res :-
  part_evalM T M,
  bind_effM M simplify_snd Res.

part_evalM (inl T) Res :-
  part_evalM T M,
  bind_effM M (V\ unit_value_effM (inl V)) Res.

part_evalM (inr T) Res :-
  part_evalM T M,
  bind_effM M (V\ unit_value_effM (inr V)) Res.

part_evalM (case CT LF RF) Res :-
  part_evalM CT M,
  bind_effM M (CV\ simplify_case CV LF RF) Res.

part_evalM (lam F1) Res :-
  part_eval_fun F1 F2,
  unit_value_effM (lam F2) Res.

part_evalM (rec F1) Res :-
  pi f\ sigma Mf\
    unit_comp_effM f Mf,
    part_evalM f Mf =>
      sigma Fx\
        part_eval_fun (F1 f) Fx,
        ( % CASE: function not recursive anymore -> normal function
          unit_value_effM (lam Fx) Res
        ; % CASE: function still potentially recursive
          F2 f = Fx,
          unit_comp_effM (rec F2) Res
        ).

part_evalM (app T1 T2) Res :-
  part_evalM T1 M1,
  part_evalM T2 M2,
  bind_effM M1 (V1\ bind_effM M2 (simplify_app V1)) Res.

part_evalM (abs_rtp T) Res :-
  part_evalM T M,
  bind_effM M (V\ unit_value_effM (abs_rtp V)) Res.

part_evalM (rep_rtp T) Res :-
  part_evalM T M,
  bind_effM M simplify_rep_rtp Res.


% PART_EVAL_FUN

part_eval_fun F1 F2 :-
  pi x\ sigma Mx\
    unit_value_effM x Mx,
    part_evalM x Mx =>
      sigma M\
        part_evalM (F1 x) M,
        show_effM M (F2 x).


% SIMPLIFICATION RULES

type simplify_pair tm -> tm -> effM tm -> o.
type simplify_fst tm -> effM tm -> o.
type simplify_snd tm -> effM tm -> o.

type simplify_case tm -> (tm -> tm) -> (tm -> tm) -> effM tm -> o.
type simplify_case_arm tm -> (tm -> tm) -> (tm -> tm) -> (tm -> tm) -> o.
type simplify_case_arms tm -> (tm -> tm) -> (tm -> tm) -> effM tm -> o.

type simplify_app tm -> tm -> effM tm -> o.
type simplify_term_app tm -> tm -> effM tm -> o.

type simplify_rep_rtp tm -> effM tm -> o.

% Pair reconstructs its destructed form -> simplify.
% This is safe, because V, too, is guaranteed to be a value!
simplify_pair V1 V2 Res :-
  lifted_term V1 (fst V),
  lifted_term V2 (snd V),
  !,
  unit_value_effM V Res.

simplify_pair V1 V2 Res :- unit_value_effM (pair V1 V2) Res.

simplify_fst (pair V1 _V2) Res :- !, unit_value_effM V1 Res.
simplify_fst V Res :- unit_comp_effM (fst V) Res.

simplify_snd (pair _V1 V2) Res :- !, unit_value_effM V2 Res.
simplify_snd V Res :- unit_comp_effM (snd V) Res.

simplify_case (inl V) LF _RF Res :- !, part_evalM (LF V) Res.
simplify_case (inr V) _LF RF Res :- !, part_evalM (RF V) Res.

% Condition not reducable to choice.
simplify_case CV LF1 RF1 Res :-
  part_eval_fun LF1 LF2,
  part_eval_fun RF1 RF2,
  simplify_case_arm CV LF2 inl LF3,
  simplify_case_arm CV RF2 inr RF3,
  simplify_case_arms CV LF3 RF3 Res.

% Case arm a function of condition.
simplify_case_arm CV F1 Make F2 :-
  pi x\ sigma Mx\
    unit_value_effM x Mx,
    part_evalM x Mx =>
      sigma F\ sigma M\
        elim_sub_term (F1 x) (Make x) F,
        !,
        part_evalM (F CV) M,
        show_effM M (F2 x).

% Case arm not a function of condition.
simplify_case_arm _CV F _Make F.

% Left and right case arm equivalent.
simplify_case_arms CV LF RF Res :-
  pi l\ pi r\
    EQ = LF l,
    EQ = RF r,
    !,
    part_evalM EQ Res.

% Case arms not equivalent.
simplify_case_arms CV LF RF Res :- unit_comp_effM (case CV LF RF) Res.

% Application of simple lambda abstraction.
simplify_app (lam F) V Res :- !, part_evalM (F V) Res.

% Terminating function applications.
simplify_app FV V Res :-
  funcall_terminates FV V,
  !,
  simplify_term_app FV V Res.

% Maybe non-terminating function applications.
simplify_app FV V Res :- unit_mnont_effM (app FV V) Res.

% Terminating recursive function application.
simplify_term_app FV V Res :-
  FV = rec F,
  !,
  part_evalM (F FV V) Res.

% Terminating unknown function.
simplify_term_app FV V Res :- unit_comp_effM (app FV V) Res.

simplify_rep_rtp (abs_rtp V) Res :- !, unit_value_effM V Res.
simplify_rep_rtp V Res :- unit_comp_effM (rep_rtp V) Res.


% SHOW_EFFM

show_effM (value_effM T) T.
show_effM (mnont_effM T F) (let_mnont T G) :- pi t\ show_effM (F t) (G t).
show_effM (comp_effM T F) (let_comp T G) :- pi t\ show_effM (F t) (G t).


% SPECIAL RULES FOR LIFTED TERMS

part_evalM LT Res :-
  (
    let T F = LT
  ;
    let_mnont T F = LT
  ;
    let_comp T F = LT
  ),
  part_evalM T M,
  bind_effM M (V\ part_evalM (F V)) Res.

part_evalM LT Res :-
  lifted_term LT _T,
  unit_value_effM LT Res.
