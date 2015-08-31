module debug.
accumulate lists.

type bracket          string -> string -> o -> string -> o.  % Auxiliary

bracket Pre St G Post :- print Pre, print St, term_to_string G S, print S, print Post.
announce G :- bracket ">>" "" G "\n", fail.

spy St G :- ((bracket ">>> " St G "\n", G, bracket "+++ " "" G "\n");
          (bracket "<<< " "" G "\n", fail)).


if P Q R :- P, !, Q.
if P Q R :- R.
