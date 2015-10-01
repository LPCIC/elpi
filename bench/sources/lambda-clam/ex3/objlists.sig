/*

File: objlists.sig
Author: Louise Dennis
Description: A Theory for Lists
Last Modified: 20th March 2001

*/

sig objlists.

accum_sig arithmetic.

type	objlists theory.

type    olist   osyn -> osyn.

type    onil         osyn.
type    ocons        osyn.
type    oapp         osyn.
type    olength      osyn.
type    orev         osyn.
type    allList 	osyn.

type    oapp1           rewrite_rule.
type    oapp2           rewrite_rule.
type    ass_oapp        rewrite_rule.
type    cons_functional rewrite_rule.
% type    neq_cons_nil    rewrite_rule.
% type    neq_nil_cons    rewrite_rule.
type    m1	        rewrite_rule.
type    olength1        rewrite_rule.
type    olength2        rewrite_rule.
type    orev1           rewrite_rule.
type    orev2           rewrite_rule.
type    allList1        rewrite_rule.
type    allList2        rewrite_rule.
type    allList_or_l    rewrite_rule.
type    allList_or_r    rewrite_rule.

type assapp         query.
type all_list       query.
type all_list_cv    query.
type all_list_sy    query.
type allList_and_dist query.
type allList_and_dist_cv query.
type allList_or_left  query.
type allList_or_right query.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  INDUCTION SCHEMES FOR LISTS
%%

type list_struct       scheme.
type list_twostep      scheme.

end

