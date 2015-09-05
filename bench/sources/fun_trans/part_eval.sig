sig part_eval.

accum_sig let_ext.
accum_sig effect_monad.

% PARTIAL EVALUATION WITH EFFECT ANALYSIS

% [part_eval +T1 ?T2] partially evaluates term [T1] to [T2]. The
% effect behaviour (non-termination, impureness) of [T1] is
% preserved. Side-effecting terms are lifted to the outermost level
% (toplevel or function abstractions). See module "let_ext" for additional
% terms associated with lifting out side effects.
type part_eval tm -> tm -> o.

% [part_eval_fun +F1 ?F2] partially evaluates term function [F1] to
% [F2]. The effect behaviour (non-termination, impureness) of [F1]
% is preserved.
type part_eval_fun (tm -> tm) -> (tm -> tm) -> o.

% [funcall_terminates +F +T] checks whether function [F] (in term
% representation) terminates when applied to term [T]. There are
% no defaults for this, of course, but you may "plug in" your own
% termination analyser.
type funcall_terminates tm -> tm -> o.
