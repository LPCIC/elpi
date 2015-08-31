module binary_res_fol_nosub.

% Proving the sequent can be proved by deciding clauses C1, C2 and some other clause.

store_kc (dlist C1 C2) _ lit (dlist C1 C2).
store_kc (dlist2 C1) _ lit (dlist2 C1).
store_kc dlist3 _ lit dlist3.
andPos_ke (dlist C1 C2) _  (dlist C1 C2) (dlist C1 C2).
andPos_ke (dlist2 C1) _  (dlist2 C1) (dlist2 C1).
andPos_ke dlist3 _  dlist3 dlist3.
orNeg_kc (dlist C1 C2) _  (dlist C1 C2).
orNeg_kc (dlist2 C1) _  (dlist2 C1).
orNeg_kc dlist3 _  dlist3.
initial_ke (dlist _ _) _.
initial_ke (dlist _ _) _.
initial_ke (dlist2 _) _.
initial_ke dlist3 _.
initial_ke done _.
release_ke (dlist C1 C2) (dlist C1 C2).
release_ke (dlist2 C1) (dlist2 C1).
release_ke dlist3 dlist3.
% here we decide the clauses for proving -C1,-C2,C3 of decide depth 3.
% Note that since they might be negative, we will need sometimes to decide on the cut formula
% This cut formula is indexed by lit but all other resolvents from previous
% steps are indexed by idx, so we need to either decide on C1, C2 or lit
decide_ke (dlist (rid I) C2)  I (dlist2 C2).
decide_ke (dlist C1 (rid I))  I (dlist2 C1).
decide_ke (dlist C1 C2) lit (dlist2 C1).
decide_ke (dlist C1 C2) lit (dlist2 C2).
decide_ke (dlist2 (rid I)) I dlist3.
decide_ke (dlist2 _) lit dlist3.
decide_ke dlist3 lit done.
% the last cut is over t+ and we need to eliminate its negation
false_kc (dlist C1 C2) (dlist C1 C2).
% clauses are in prefix normal form and we just apply the sub in the right order
some_ke (dlist2 C) _ (dlist2 C).
some_ke (dlist2 C) _ (dlist2 C).
some_ke dlist3 _ dlist3.
some_ke dlist3 _ dlist3.
