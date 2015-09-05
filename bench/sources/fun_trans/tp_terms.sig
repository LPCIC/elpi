sig tp_terms.

accum_sig poly_typing.

% ABSTRACT SYNTAX WITH TYPE ANNOTATIONS OF A SIMPLE FUNCTIONAL LANGUAGE

kind tp_astK type.  % kind of typed AST-nodes
kind tp_tm type.    % kind of typed terms

type tp_ast tp_tm -> tp -> tp_astK.  % constructor for typed AST-nodes


% TYPE ANNOTATED TERMS OF THE LANGUAGE

type tp_u tp_tm.

type tp_pair tp_astK -> tp_astK -> tp_tm.
type tp_fst tp_astK -> tp_tm.
type tp_snd tp_astK -> tp_tm.

type tp_inl tp_astK -> tp_tm.
type tp_inr tp_astK -> tp_tm.

type tp_case tp_astK -> (tp_astK -> tp_astK) -> (tp_astK -> tp_astK) -> tp_tm.

type tp_lam (tp_astK -> tp_astK) -> tp_tm.
type tp_rec (tp_astK -> tp_astK -> tp_astK) -> tp_tm.
type tp_app tp_astK -> tp_astK -> tp_tm.

type tp_abs_rtp tp_astK -> tp_tm.
type tp_rep_rtp tp_astK -> tp_tm.

type tp_tlam tp -> (tp_astK -> tp_astK) -> tp_tm.
type tp_trec tp -> (tp_astK -> tp_astK -> tp_astK) -> tp_tm.
type tp_tlet schema -> tp_astK -> (tp_astK -> tp_astK) -> tp_tm.
type tp_tabs (tp -> tp_astK) -> tp_tm.


% BASIC OPERATIONS ON TYPED TERMS, ABSTRACT SYNTAX TREES AND FUNCTIONS
% ON TYPED TERMS

% [make_tp_ast +TM ?TP_AST] takes a normal term [TM] and converts it to
% a type annotated AST-node [TP_AST].
type make_tp_ast tm -> tp_astK -> o.

% [tp_ast_get_term +TP_AST ?TP_TM] accesses the term part of typed
% AST-node [TP_AST] and returns the typed term in [TP_TM].
type tp_ast_get_term tp_astK -> tp_tm -> o.

% [tp_ast_get_type +TP_AST ?TP] accesses the type part of typed AST-node
% [TP_AST] and returns the result in [TP].
type tp_ast_get_type tp_astK -> tp -> o.

% [tp_tm_fun_linear +[TP_ASTF]] tests whether function [TP_ASTF] on typed
% AST-nodes is linear in its argument, i.e. the number of occurrences
% of its parameter in the function body is 0 or 1, considering different
% case arms separately.
type tp_tm_fun_linear (tp_astK -> tp_astK) -> o.

% [output_tp_ast +Out +TP_AST] prints typed AST-node [TP_AST] to output
% stream [Out].
type output_tp_ast out_stream -> tp_astK -> o.

% [print_tp_ast +TP_AST] prints typed AST-node [TP_AST] to standard
% output.
type print_tp_ast tp_astK -> o.


% INTERNAL OPERATIONS - USE WITH CAUTION
type tp_tm_linear_aux tp_astK -> o -> o -> o.
type tp_tm_fun_linear_aux (tp_astK -> tp_astK) -> o -> o -> o.
