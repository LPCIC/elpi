module control.

type if          o -> o -> o -> o.
type once        o -> o.


% Relates three formulas if the corresponding condition holds:
% ``if Cond Then Else'' attempts to prove Then if the condition Cond
% success; otherwise it attempts Else.  Notice the use of !.

if Cond Then Else :- Cond, !, Then.
if Cond Then Else :- Else.

% Attempts to prove its argument and if it succeeds, backtracking is
% disallowed by using !.

once P :- P, !.

type announce o -> o.

announce G :-
  print ">> ", term_to_string G String, print String, print "\n", fail.


type spi o -> o.

spi G :-
  (print ">Entering ", term_to_string G Str,  print Str,  print "\n", G,
   print ">Success  ", term_to_string G Strx, print Strx, print "\n";
   print ">Leaving  ", term_to_string G Str,  print Str,  print "\n", fail).
