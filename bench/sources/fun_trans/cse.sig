sig cse.

accum_sig terms.
accum_sig let_ext.

% [elim_cse +T1 ?T2] eliminates common sub-computations from term [T1],
% returning the result in [T2]. Returns [T1] if no such sub-computations
% exist. The sub-computations must be identified with "let_comp", as is
% done, for example, by the partial evaluator ("part_eval").
type elim_cse tm -> tm -> o.
