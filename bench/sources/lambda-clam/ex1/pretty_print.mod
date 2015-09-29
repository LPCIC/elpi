/*

File: pretty_print.mod
Author: Alan Smaill / James Brotherston
Description:  Pretty printing primitives based on Paulson's ML example
Last Modified: 14th August 2002.

*/

module pretty_print.

% local declarations

local  width   int -> o.
          % no clauses for this, used to hand value to printing routine
          % via implication goal.
local  outstream   out_stream -> o.  % same story          
local  breakdist   list thing -> int -> int -> o.
local  p_length    thing -> int -> o.
local  sum         list thing -> int -> int -> o.
local  blanks      int -> string -> string -> o.
local  printing    list thing -> int -> int -> int -> int -> o.
local  printOne    thing -> int -> int -> int -> int -> o.
local  abPrinting  A -> (A -> list thing) -> int -> int -> int -> int -> o.
local  block       list thing -> int -> int -> thing.
          % block has size info, in addition to blo info
local  abstraction (A -> list thing) ->  int -> int -> thing.
          % same idea for abstracted object
local  makeBlocks  thing -> thing -> o.
          % conversion from blo to block representation.

local mappred      list A -> (A -> B -> o) -> list B -> o.

mappred nil P nil.
mappred (X::L) P (Y::K) :- P X Y, mappred L P K.


% see Paulson, ML for the working programmer, Ch 8
% (on imperative programming!)

breakdist ((block _ _ Len)::Rest) After Result :-
          breakdist Rest After New,
          Result is Len + New.
breakdist ((abstraction _ _ Len)::Rest) After Result :-
          breakdist Rest After New,
          Result is Len + New.
breakdist ((str S)::Rest) After Result :-
           breakdist Rest After New,
           Result is (size S) + New.
breakdist ((lvar S)::Rest) After Result :-
          breakdist Rest After New,
          Result is 8 + New.
breakdist ((brk _)::Rest) After 0.
breakdist nil After After.

p_length (block _ _ Len) Len.
p_length (abstraction _ _ Len) Len.
p_length (str S) L :- L is (size S).
p_length (brk Len) Len.
p_length (lvar _) 8.  % must do better ...

sum nil N N.
sum (H::T) N M :- p_length H L, Next is N + L, sum T Next M.

blanks N _ _ :- N < 0, print "neg argument to blanks/3 !\n", !, fail.
blanks 0 S S :- !.
blanks N S T :- M is N - 1, SS is " " ^ S, blanks M SS T.

%  extra (last) 2 arguments to printing are space left on current line,
%  first before, and second after the call succeeds.

printing nil _ _ S S.

printing ((str S)::Rest) BlockSpace After Space SS :-
	Newspace is Space - (size S),
        outstream Stream,
        output Stream S,
        printing Rest BlockSpace After Newspace SS.

printing ((lvar T)::Rest) BlockSpace After Space SS :-
	Newspace is Space - 8,
        outstream Stream,
        printterm Stream T,
        printing Rest BlockSpace After Newspace SS.

printing ((brk Len)::Rest) BlockSpace After Space  SS:- 
	breakdist Rest After Bdist,
	Len + Bdist =< Space, !,    % will it fit in this line?
        Newspace is Space - Len,
	blanks Len "" B,
	outstream Stream,
        output Stream B,
        printing Rest BlockSpace After Newspace SS.

printing ((brk Len)::Rest) BlockSpace After Space SS :- 
                               % doesn't fit in the current line --
                               % might generate blank chars to fill
                               % line, as Paulson does
        width W,
        Blanks is W - BlockSpace,
        Newspace is W - Blanks,
        blanks Blanks "" B,
	outstream Stream,
	output Stream "\n",
        output Stream B,
        printing Rest BlockSpace After Newspace SS.

printing ((block Bes Indent Len)::Rest) BlockSpace After Space SS :-
	NewBspace is Space - Indent,
	breakdist Rest After Bdist,
	printing Bes NewBspace Bdist Space NS,
        printing Rest BlockSpace After NS SS.

printing ((abstraction A Indent Len)::Rest) BlockSpace After Space SS :-
	NewBspace is Space - Indent,
	breakdist Rest After Bdist,
      	outstream Stream,
        pi var \ ( printing (A var) NewBspace Bdist Space NS),
        printing Rest BlockSpace After NS SS.

        % next computes block sizes -- still of type thing

        % unlike SML, need to map this
makeBlocks (blo Indent Es) (block NewEs Indent Z) :- !,
        mappred Es makeBlocks NewEs,     
	sum NewEs 0 Z.
makeBlocks (abstr Indent A) (abstraction New Indent Len) :- !,
        pi zz\ (mappred (A zz) makeBlocks (New zz),
                sum (New zz) 0 Len).
makeBlocks X X.

pr Outstream Thing Width :-
	makeBlocks Thing BThing,
        (width Width => outstream Outstream =>
	    printing (BThing :: nil) Width 0 Width _).

                             




end
