module slim_deadlock.

%%%%%%%%%%%%%%%%%%%%%%%%%%% Syntax of programs

% T ::= int | object
% F ::= T | fut T
% M ::= method T METHODNAME T x\B
% P ::= method list                            the main is called main
% B ::= decl F x\ B | S
% S ::= skip | x <- Z | if-then-else E S S | return E | S - S | await E
% Z ::= E | call NAME E E | new | get E
% E ::= V | x | this | ...
% V ::= null | prim

infix  <-  155.

%%%%%%%%%%%%%%%%%%%%%%%%%%% Syntax of contracts

% R ::= primitive | ???? | OBJECTNAME | requires OBJECTNAME R
% C ::= 0 | dget OBJECTNAME OBJECTNAME | dawait OBJECTNAME OBJECTNAME
%     | dcall METHODNAME R R OBJECTNAME | C - C | C + C
% X ::= R | FUTURENAME
% Z ::= async R | sync R
% MC ::= method_contract receiver\ argument\ C R   ???receiver,argument=R???

% ???????????????

%%%%%%%%%%%%%%%%%%%%%%%%%%% Contract inference

% T-Var
% T-Fut
of2 Gamma E R :- mem (ofi E R) Gamma.

% T-Value
of2 Gamma E R :- of2 Gamma E F, of2 F (sync R).
of2 Gamma E R :- of2 Gamma E F, of2 F (async R).

% T-Val
of2 Gamma prim primitive.

%% T-Null
of2 Gamma null primitive.

% T-Pure
of _ Gamma E R 0 Gamma :- of2 Gamma E R.

% T-Get
of O Gamma (get E) X (dget O O') [ofi F (sync R) | Gamma'] :-
 unbind F Gamma Gamma', % remove the binding of F from Gamma
 of2 Gamma E F, of2 Gamma F (async R), $delay (R = requires O' X) Z /*???*/.

% T-Get-Tick
of O Gamma (get E) X 0 Gamma :-
 of2 Gamma E F, of2 Gamma F (sync R), $delay (R = requires O' X) Z /*???*/.

% T-New
of O Gamma new O 0 Gamma.

% T-AInvk: TODO

% T-Skip
ofs O Gamma skip 0 Gamma.

% T-Assign
ofs O Gamma (X <- Z) C [ofi X X'' | Gamma'] :-
 % Bug: fare unbinding di X in Gamma'
 mem Gamma (ofi X X'), of O Gamma Z X'' C Gamma'.

% T-Await: TODO

% T-Await-Tick: TODO

% T-If: TODO

% T-Seq: TODO

% T-Return: TODO

%%%%%%%%%%%%%%%%%%%%%%%%%%% Library functions

mem [X|_] X.
mem [_|L] X :- mem L X.
