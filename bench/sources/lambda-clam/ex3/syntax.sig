/*

File: syntax.sig
Author: Louise Dennis / James Brotherston
Description:  Support for lclam HOAS syntax.
Last Modified: 13th August 2002

*/

sig syntax.

accum_sig basic_types.
accum_sig lclam_utils.

kind osyn type.
kind hyp_ann type.

% type synmemb  (osyn -> list osyn -> o).

type otype_of osyn -> osyn -> osyn.
type abs (osyn -> osyn) -> osyn.
type app osyn -> osyn -> osyn.
type tuple (list osyn) -> osyn.

type nha hyp_ann.
type hyp osyn -> hyp_ann -> osyn.

type counting int -> osyn.
type counting_abs int -> osyn -> osyn.

%% Constructors for syntax introduced by users in library files.
type user_object string -> osyn.

%% Constructors for syntax types 
type    arrow   osyn -> osyn -> osyn.
type    tuple_type (list osyn) -> osyn.

infixr arrow 100.

%% Base constructors
type obj        osyn.    % this type is intended to have no special properties,
                         % e.g. induction schemes, rewrite rules etc.
% for embedding wildcard -- can this be done more directly via HO vars?
type universe   osyn.	 % This is supposed to be a type for types (it does not
			 % contain itself.

%%  Utility functions (not sure what function triv really serves)
type obj_atom     osyn -> o.
type subterm_of   osyn -> osyn -> (list int) -> o.
type replace_with osyn -> osyn -> osyn -> osyn -> o.
type replace_at   osyn -> osyn -> osyn -> (list int) -> o.
type copy_term    osyn -> osyn -> o.

%% replacing flex
type headvar_osyn osyn -> o.

% Asserts that a term represents a universal variable
% (i.e. it is the result of passing thru a forall_node2).

type univ_var   osyn -> osyn -> o.

type has_otype  theory -> osyn -> osyn -> o.
type has_otype_ osyn -> osyn -> o.
type env_otype  osyn -> (list osyn) -> osyn -> o.

%% For defining object types - the lists are for constructors (base case and 
%% step case ones).

type is_otype   theory -> osyn -> (list osyn) -> (list osyn) -> o.

end
