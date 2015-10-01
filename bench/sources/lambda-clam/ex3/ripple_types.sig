/*

File: ripple_types.sig
Author: Louise Dennis
Description: Defines the types used in rippling
Last Modfied: 19th March 2001

*/

sig ripple_types.

accum_sig rewrite_types.

kind   etree     type.   % Embedding
kind   dir       type.   % Wave front direction
kind   subst     type.
kind   scheme    type.
kind   mkey      type.

type   red       mkey.
type   nored     mkey.

type   embed     theory.

type   wild_card osyn.

% three possible wave front directions - in, out and both

type   inward    dir.
type   outward   dir.
type   inout	 dir.

/*
kind wffl type.

type wfflag dir -> wffl -> dir.
type iswf wffl.
type notwf wffl.
*/

% tree constructors for embedding trees.
%
% Note that an embedding tree "matches" the skeleton term tree until
% leaves are reached, but that the tree is "labelled" with the address of 
% the node in the full term.
  
type   dummytree etree. 
type   leaf      dir -> (list int) -> etree.
type   sink      dir -> (list int) -> etree.

/* here because it makes thinks compile - no really!
I put it in because I thought I needed it (I didn't) and then
couldn't take it out again. */
% type   wsink      dir -> (list int) -> etree.
type   node      dir -> (list int) -> etree -> etree -> etree.
type   node2     dir -> (list int) -> (list etree) -> etree.

type   empty     subst.
type   repl      osyn -> osyn -> subst.
type   dom       (osyn -> subst) -> subst.

type   ripGoal   osyn -> (list osyn) -> (list etree) -> goal. 
						       % in rippling,
                                                       % goal has skel
                                                       % and embed also.
type   exRipGoal osyn -> (list osyn) -> (list etree) -> int -> goal.


type induction_schemes_list_ (list scheme) -> o.
type induction_schemes_list (list scheme) -> o.
type induction_scheme        theory -> scheme -> osyn -> subst -> osyn -> goal -> goal -> o.

end
