/*

File: logic_eq_constants.sig
Author: Louise Dennis / James Brotherston
Description: Basic declarations for logic with equality
Last Modified: 20th August 2002

*/

sig logic_eq_constants.

accum_sig pretty_printer.

type    bool    osyn.

type    and     osyn.
type    or      osyn.
type    imp     osyn.
type    neg     osyn.
type    forall  osyn.
type    exists  osyn.
type    falseP  osyn.
type    trueP   osyn.
type    iff     osyn.
type    xor     osyn.
% type    ifthen  osyn.

type    eq      osyn.
type    neq     osyn.

type transitive osyn.

%----------------------------------
% Method names

type existential     meth.
type trivial         meth.
type imp_i           meth.
type imp_e           meth.
type and_i           meth.
type and_e           meth.
type or_il           meth.
type or_ir           meth.
type or_e            meth.
type false_e         meth.
type all_i           meth.
type exists_i        meth.
type all_e           meth.
type allFi           meth.
type redundant       meth.   % get rid of "vacuous" quantification
type neg_i           meth.
type neg_e           meth.
type trivially_false meth.
type imp_e1          meth.
type imp_e2          meth.
type imp_e3          meth.
type imp_e4          meth.
type impe_rule       meth -> osyn -> osyn -> osyn -> goal -> o.

%% Compound methods

type taut            meth.

type  idty rewrite_rule.
type  beta_reduction  rewrite_rule.
type  beta_idty  rewrite_rule.

type replace_in_hyps   (list osyn)  -> osyn -> (list osyn) -> (list osyn) -> o.
type forall_elim osyn -> osyn -> osyn -> osyn -> o.

type from_imp hyp_ann.

end
