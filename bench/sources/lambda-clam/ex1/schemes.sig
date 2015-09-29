/*

File: schemes.sig
Author: Louise Dennis / James Brotherston
Description: Induction Scheme Support
Last Modified: 20th August 2002

*/

sig schemes.

accum_sig embed.

type measured                osyn -> (osyn -> osyn) -> osyn.
type free                    osyn -> (osyn -> osyn) -> osyn.

type and_scheme scheme -> scheme -> scheme.
type no_scheme  scheme.

type applicable_induction_scheme   scheme -> subst -> goal -> int -> goal -> o.

type all_ripple_analysis     int -> (list osyn) -> osyn ->
                               (list subst) -> 
                               o.

%% From rewriting.sig (not accumulated until further up)

type rewr rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o.  

end
