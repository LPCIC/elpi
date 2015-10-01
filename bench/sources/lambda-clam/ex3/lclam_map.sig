/*

File: lclam_map.sig
Author: Louise Dennis / James Brotherston
Description:  Mapping predicates
Last Modified: 13th August 2002

*/

sig lclam_map.

accum_sig lclam_list.

type mapfun	      list A -> (A -> B) -> list B -> o.
type mappred          list A -> (A -> B -> o) -> list B -> o.
type for_each	      list A -> (A -> o) -> o.
type for_each_cut     list A -> (A -> o) -> o.
type for_one          list A -> (A -> o) -> A -> o.

/*
type map_app (list A) -> (A -> (list B) -> o) -> (list B) -> o.
type map_app2 (list A) -> (list B) -> (A -> B -> (list C) -> o) -> (list C) -> o.
*/

type forthose list A -> (A -> B -> C -> o) -> list B -> list C -> o.
%% type forthose2 list A -> (A -> B -> C -> o) -> list B -> list C -> list A -> list D -> list D -> o.

type mappred2 (list A) -> (A -> B -> C -> o) -> (list B) -> (list C) -> o.

type mapcount (list A) -> (A -> B -> C -> int -> o) -> (list B) -> (list C) -> int -> o.

/*
type filter (list A) -> (A -> B -> o) -> (list B) -> o.
*/
type filter2 (list A) -> (list B) -> (list C) -> (list D) -> (list D) -> (A -> B -> C -> o) -> o.

/* type mapbuild (B -> B -> B) -> (list B) -> B -> o. */

end
