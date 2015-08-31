module eprover.

%accumulate binary_res_fol_nosub.
accumulate paramodulation.

% gets a sequent |- A !-! B, C, D !-! E, etc.

%binary rules, use the right indices and the right resolution certificate
% eprover doesnt distinct between the from and into clauses so we try both directions
cut_ke (rsteps [PM | RS] St) K C1 C2 :-
  param_rule PM I1 I2 I,
  cut_ke (rsteps [ resolv (pid (idx I1)) (pid (idx I2)) I | RS] St) K C1 C2. % paramodulation step
cut_ke (rsteps [PM | RS] St) K C1 C2 :-
  param_rule PM I1 I2 I,
  cut_ke (rsteps [ resolv (pid (idx I2)) (pid (idx I1)) I | RS] St) K C1 C2. % paramodulation step


%unary rules, just track the indices

%ignore rules
cut_ke (rsteps [ER | RS] S) K C1 C2 :-
  ignore_rule ER,
  cut_ke (rsteps RS S) K C1 C2.
decide_ke (rsteps [ER | RS] S) A B :-
  ignore_rule ER,
  decide_ke (rsteps RS S) A B.
store_kc (rsteps [ER | RS] S) A B C :-
  ignore_rule ER,
  store_kc (rsteps RS S) A B C.

param_rule (pm (id (idx I1)) (id (idx I2)) I) I1 I2 I.
param_rule (rw (id (idx I1)) (id (idx I2)) I) I1 I2 I.
ignore_rule (cn (id (idx I1)) I2).
