module runner.

accumulate col016.
accumulate col037.
accumulate col052.
accumulate col060.
accumulate col061.
accumulate col062.
accumulate col063.
accumulate col064.
accumulate col065.
accumulate rob030.

accumulate lists.
accumulate debug.

parseInput [(pr I Cl)] f- [] NCl [I] :-
  negateForm Cl NCl.

parseInput [(pr I Cl) | Ls] F Il (NCl !-! F2) [I | Il2] :-
  parseInput Ls F Il F2 Il2,
  negateForm Cl NCl.

negateMap [] [].
negateMap [(pr I Cl) | Map] [(pr I NCl) | Map2] :-
  negateForm Cl NCl,
  negateMap Map Map2.

run :-
  resProblem Name Ls (resteps C) (map Map),
  parseInput Ls f- [] F Istate,
  print "Running on problem ", print Name, print ":\n",
  negateMap Map Map2,
  resolve Map2 F (rsteps C (istate Istate)).

run :-
  problem Name F Cert (map Map),
  print "Running on problem ", print Name, print ":\n",
  resolve Map F Cert.

run.

resolve [] F Cert :-
  if (entry_point Cert F)
      (print "Success\n==============================================\n")
		  (print "Fail\n", halt), fail.
resolve [(pr I C) | R] F Cert :-
  mapsto I C => resolve R F Cert.
