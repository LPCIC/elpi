sig oper_sem.

accum_sig terms.

% CALL-BY-VALUE OPERATIONAL SEMANTICS

% [eval +T1 ?T2] reduces term [T1] to weak-head normal form (WHNF),
% the result being returned in [T2].
type eval tm -> tm -> o.
