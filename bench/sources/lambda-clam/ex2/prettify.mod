/*

File: prettify.mod
Author: Alan Smaill / James Brotherston
Description:  Mark up syntax for the pretty printer
Last Modified: 14th August 2002.

*/

module prettify.

accumulate pretty_print.

local prettify_term_list list osyn -> thing -> o.

prettify_term X (str XX) :-
	headvar_osyn X, !, % what to do with meta-variables?
        term_to_string X S,  % need to call this with fresh output var,
        S = XX.              % and then do the unification.
prettify_term (app F Args) (blo 0 [FF, str " ", AA ]) :-
	headvar_osyn F,
	!, prettify_term F FF, prettify_term Args AA.   
prettify_term X Str:-
	prettify_special X Str.
prettify_term  (otype_of X Y) (blo 0 [XX, str ":", YY]) :- !,
                 prettify_term X XX, prettify_term Y YY.
prettify_term  (hyp Y _) YY :- !,
                 prettify_term Y YY.
prettify_term  (user_object S) (str S) :- !.
prettify_term  (tuple T) (blo 1 [str "(", PT, str ")"] ) :- !,
                  prettify_term_list T PT.
prettify_term (app F Args) (blo 0 [FF, str " ", AA ]) :-
	!, prettify_term F FF, prettify_term Args AA.   


prettify_term (abs F) (abstr 1 (a\ [ lvar a, str "\\.", Body a ] )) :- !, 
          pi z\ ( prettify_term (F z) (Body z) ).



prettify_term obj (str "obj").
prettify_term V (lvar V).
prettify_term_list [T] (blo 0 [PT]) :- !,  prettify_term T PT.
prettify_term_list [H|Rest] (blo 0 [PH, str ",", brk 1| PRest]) :- !,
                  prettify_term H PH,
                  prettify_term_list Rest (blo _ PRest).

local pretty_show_hyp  osyn -> o.

pretty_show_hyp H :- pretty_show_term H, print "\n".

pretty_show_term  T :- prettify_term T PT,
                       pr std_out PT 78.

% better to deal with pretty_show_goal via prettify
% than directly as below

pretty_show_goal  (seqGoal (Hyps >>> Conc)) :- !,
                       for_each Hyps pretty_show_hyp,
                       prettify_term Conc PConc,
                       pr std_out (blo 0 [str ">>> ", PConc]) 78,
                       print "\n".
pretty_show_goal  trueGoal  :- !, print "trueGoal!\n".
pretty_show_goal  falseGoal  :- !, print "Warning: falseGoal!\n".
pretty_show_goal  (ripGoal Seq _ _) :- !,
                      pretty_show_goal (seqGoal Seq).
pretty_show_goal (G1 ** G2) :-
                      print "andGoal\n",
                      pretty_show_goal G1,
                      print "   **\n",
                      pretty_show_goal G2,
                      print "\n".
pretty_show_goal (allGoal X F) :-
                      print "allGoal (",
                      pi z\ ( printterm std_out z,
                              print "\\\n",
                              pretty_show_goal (F z),
                              print ")\n"
                            ).

pretty_show_goal G :-
	pretty_show_goal_special G, !.
pretty_show_goal G :- print "Don't know how to display goal:\n",
                      printterm std_out G,
                      print "\n".

end
