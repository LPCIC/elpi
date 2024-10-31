:- module various.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.
:- import_module list.

:- pred q(int::in, int::(free>>ground)) is semidet.
q(3,Y) :- (if (W = 2 + 1, W = 4) 
  then (W = 3 + 1, Y = 2) 
  else (W = 3 + 1, W = 88,Y = 3)). % The W in this branch in not the same as the one in the Cond and Then

:- pred nd1(int::out, int::(free>>free)) is det. % Why this works ?
nd1(2,_).
nd1(_,_) :- fail.

:- pred mult(int::out, int::out) is multi.
mult(2,3).
mult(4,4).
mult(4,5).

:- inst ll == bound([] ; [free | ll]).

:- pred wlist(list(int)).
:- mode wlist(free >> ll) is multi.
wlist([]).
wlist([_]).
% wlist([A,A]). % Invalid: two time the same variable in the list

:- pred twoints(int::in, int::in) is semidet.
twoints(A,A).
% twoints(A,A) :- wlist([]). % Invalid

:- pred failing is failure.
failing :- fail.

:- pred nondeter(int::in, int::out) is nondet.

nondeter(0,3) .
nondeter(0,5) .
nondeter(1,4) :- 2 = 1 + 3.
nondeter(2,5) :- mult(1,2).

:- pred x(io::di, io::uo) is det.

x(!_IO) :- 
  % q(3,Y), % q is semidet, so should be x
  mult(_X,_Y), % THIS IS OK, since mult succeeds at least once
  % mult(X,_Z), mult(X,_W), % This makes x non deterministic: backtracking is possible
  true,
  % (if (4 > 1) then (fail) else (true)), % the condition is demidet, so the clause
  % failing, % Adding this leads to a determinacy failure
  % nondeter(1,_Y),
  true
  .

main(!IO) :- x(!IO).