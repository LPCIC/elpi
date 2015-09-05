sig tp_part_eval.

accum_sig tp_let_ext.
accum_sig effect_monad.

% PARTIAL EVALUATION OF TYPED TERMS WITH EFFECT ANALYSIS

% [part_eval +T1 ?T2] partially evaluates typed term [T1] to
% [T2]. The effect behaviour (non-termination, impureness) of [T1]
% is preserved. Side-effecting terms are lifted to the outermost level
% (toplevel or function abstractions). See module "let_ext" for additional
% terms associated with lifting out side effects.
type tp_part_eval tp_astK -> tp_astK -> o.

% [part_eval_fun +TP +F1 ?F2] partially evaluates the function on typed
% terms [F1] to [F2], assuming that the parameter to [F1] has type
% [TP]. The effect behaviour (non-termination, impureness) of [F1]
% is preserved.
type tp_part_eval_fun tp -> (tp_astK -> tp_astK) -> (tp_astK -> tp_astK) -> o.

% [funcall_terminates +F +T] checks whether function [F] (in typed
% term representation) terminates when applied to typed term [T]. There
% are no defaults for this, of course, but you may "plug in" your own
% termination analyser.
type tp_funcall_terminates tp_astK -> tp_astK -> o.
