%
%	The MU-puzzle
%		from Hofstadter's "Godel, Escher, Bach" (pp. 33-6).
%		written by Bruce Holmer
%
%	To find a derivation type, for example: 
%		theorem([m,u,i,i,u]).
%	Also try 'miiiii' (uses all rules) and 'muui' (requires 11 steps).
%	Note that it can be shown that (# of i's) cannot be a multiple
%	of three (which includes 0).
%	Some results:
%
%	string		# steps
%	------		-------
%	miui		8
%	muii		8
%	muui		11
%	muiiu		6
%	miuuu		9
%	muiuu		9
%	muuiu		9
%	muuui		9

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
module fast_mu.

once :- theorem (xcons m (xcons u (xcons u (xcons i xnil)))).
%main :- theorem (xcons m (xcons u (xcons u (xcons i xnil)))).
%main :- theorem (xcons m (xcons i (xcons i (xcons i (xcons i (xcons i xnil)))))).

iter0 zero X.
iter0 (s N) X :- X, iter0 N X.

plus0 zero X X.
plus0 (s X) Y (s S) :- plus0 X Y S.

mult0 zero X zero.
mult0 (s X) Y Z :- mult0 X Y K, plus0 Y K Z.

exp0 zero X (s zero).
exp0 (s X) Y Z :- exp0 X Y K, mult0 Y K Z.

main :-
 TEN = s (s (s (s (s (s (s (s (s (s zero))))))))),
 iter0 TEN once.


% First break goal atom into a list of characters,
% find the derivation, and then print the results.
theorem G :-
	length G GL1,
	(s GL) = GL1, 
	derive (xcons m (xcons i xnil)) G (s zero) GL Derivation zero.
  %term_to_string (xcons (rule1 zero (xcons m (xcons i xnil))) Derivation) SS, print SS.
	% nl, print_results([rule(0,[m,i])|Derivation], 0).

% derive(StartString, GoalString, StartStringLength, GoalStringLength,
%		Derivation, InitBound).
derive S G SL GL D B :- 
	% B1 is B + 1,
	% write('depth '), write(B1), nl,   
   derive2 S G SL GL (s zero) D B.
derive S G SL GL D B :- 
	B1 = (s B),
	derive S G SL GL D B1.

% derive2(StartString, GoalString, StartStringLength, GoalStringLength,
%		ScanPointer, Derivation, NumRemainingSteps).
derive2 S S SL SL Dummy1 xnil Dummy2.
derive2 S G SL GL Pin (xcons (rule1 N I) D) R :-
	lower_bound SL GL B,
	leq B R,
	(s R1) = R,
	rule_aux S I SL IL Pin Pout N,
	derive2 I G IL GL Pout D R1.

rule_aux (xcons m T1) (xcons m T2) L1 L2 Pin Pout N :- 
	rule T1 T2 L1 L2 Pin Pout (s zero) i N X X.

% rule(InitialString, FinalString, InitStrLength, FinStrLength,
%		ScanPtrIn, ScanPtrOut, StrPosition, PreviousChar,
%		RuleNumber, DiffList, DiffLink).
%   The difference list is used for doing a list concatenate in rule 2.
rule (xcons i xnil) (xcons i (xcons u xnil)) L1 L2 Pin Pout Pos Dummy1 (s zero) Dummy2 Dummy3 :- 
                       leq Pin Pos,
			              (s (s Pout)) = Pos,
			              L2 = (s L1).
rule xnil L L1 L2 Dummy1 (s zero) Dummy2   Dummy3 (s (s zero)) L xnil :-
			sum L1 L1 L2.
rule (xcons i (xcons i (xcons i T))) (xcons u T) L1 L2 Pin Pout Pos Dummy1 (s (s (s zero))) Dummy2 Dummy3 :- 
           leq Pin Pos,
			  (s Pout) = Pos,
			  (s (s L2)) = L1.
rule (xcons u (xcons u T)) T L1 L2 Pin Pout Pos i (s (s (s (s zero)))) Dummy2 Dummy3 :- 
			  leq Pin Pos,
			  (s (s Pout)) = Pos,
			  (s (s L2)) = L1.
rule (xcons H T1) (xcons H T2) L1 L2 Pin Pout Pos Dummy N L (xcons H X) :-
	        Pos1 = (s Pos),
	        rule T1 T2 L1 L2 Pin Pout Pos1 H N L X.

% print_results([], _).
% print_results([rule(N,G)|T], M) :-
% 	M1 is M + 1,
% 	write(M1), write('  '), print_rule(N), write(G), nl,
% 	print_results(T, M1).
% 
% print_rule(0) :- write('axiom    ').
% print_rule(N) :- N =\= 0, write('rule '), write(N), write('   ').
% 
lower_bound N M (s zero) :- 
         smaller N M.

lower_bound N N (s (s zero)).
%lower_bound N M B :-
%        smaller M N,
%        diff N M Diff,
%        P is Diff/\1,             % use and to do even test
%        (P =:= 0 ->
%                B is Diff >> 1;   % use shifts to divide by 2
%                B is ((Diff + 1) >> 1) + 1).
lower_bound N M B :-
        smaller M N,
        diff N M Diff,
        is_even Diff,!,
        ten2two Diff Diff1,    
        shift Diff1 Diff2,
        two2ten Diff2 B. 

lower_bound N M B :-      
        smaller M N,
        diff N M Diff,
        ten2two (s Diff) Diff1,
        shift Diff1 Diff2,
        two2ten Diff2 D,
        B = (s D).             


ten2two X XL :- ten2two_aux X RezL, rev RezL XL.
ten2two_aux zero (xcons zero xnil) :- !.
ten2two_aux (s zero) (xcons (s zero) xnil) :- !.
ten2two_aux X (xcons C SL) :- modd X (s (s zero)) C, 
                              divv X (s (s zero)) Y,
                              ten2two_aux Y SL.


length xnil zero.
length (xcons X XL) (s N) :- length XL N.

shift (xcons X xnil) xnil.
shift (xcons X XL) (xcons X ZL) :- shift XL ZL.

smaller zero (s X).
smaller (s X) (s Y) :- smaller X Y.

leq X Y :- smaller X Y.
leq X X.

diff X X zero.
diff (s X) Y (s S) :- diff X Y S. 

sum zero X X.
sum (s X) Y (s S) :- sum X Y S.

mult zero _ zero.
mult _ zero zero.
mult (s zero) X X :- !.
mult (s X) N S :- mult X N S1, sum S1 N S.

pow X zero (s zero).
pow X (s zero) X.
pow X (s N) P :- pow X N P1,!, mult X P1 P.

is_even zero.
is_even X :- modd X (s (s zero)) zero.
 
modd X Y X :- smaller X Y.
modd X Y Z :- sum X1 Y X, modd X1 Y Z.

divv X Y zero :- smaller X Y.
divv X Y (s D) :- sum X1 Y X, !, divv X1 Y D.

rev xnil xnil.
rev (xcons X XL) ZL :- rev XL RL,!, appendd RL X ZL.

appendd xnil Y (xcons Y xnil).
appendd (xcons X XL) Y (xcons X ZL) :- appendd XL Y ZL. 


two2ten (xcons X xnil) X.
two2ten (xcons X XL) R :- two2ten XL S1,  
                          length XL L,
                          pow (s (s zero)) L P, 
                          mult X P M,                          
                          sum S1 M R. 


