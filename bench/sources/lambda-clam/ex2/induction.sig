/* 

File: induction.sig
Author: Louise Dennis / James Brotherston
Description: Induction Methods
Last Modified: 20th August 2002

*/

sig induction.

accum_sig schemes, generalise, pwf.

type induction theory.

kind indtype type.

type   normal_ind   indtype.
type   with_critics indtype.
type   whisky_ind   indtype.

type   induction_meth        indtype -> scheme -> subst ->  meth.
type   fertilise             meth.
type   fertilisation_strong  meth.
type   fertilisation_weak    meth.
type   truegoalmeth	     meth.

%% New more "generic" version

type induction_top indtype -> meth.
type ind_strat     indtype -> meth.
type step_case     indtype -> meth.

type trivials           meth.
type equality_condition meth.

type triv_abs rewrite_rule.

type sink_match_     osyn -> osyn -> osyn -> o.

type ind_hyp hyp_ann.

end
