/*

File: lclam_utils.sig
Author: James Brotherston
Description: Utility functions (including findall)
Last Modfied: 13th August 2002

*/

sig lclam_utils.

accum_sig lclam_map.

/* Miscellaneous utility functions */

type findall         (A -> o) -> (list A) -> o.
type findall_sort         (A -> o) -> (list A) -> (A -> A -> o) -> o.
type on_backtracking  o -> o.

end
