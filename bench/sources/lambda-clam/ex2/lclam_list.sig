/*

File: lclam_list.sig
Author: Louise Dennis / James Brotherston
Description:  List utility functions
Last Modified: 13th August 2002

*/

sig lclam_list.

kind  pairty   type -> type -> type.
type  pair     A -> B -> (pairty A B).

type  memb           A -> (list A) -> o.
type  member         A -> (list A) -> o.
type  append        (list A) -> (list A) -> (list A) -> o.
type  length        (list A) -> int -> o.
type  nth           (list A) -> int -> A -> (list A) -> o.
type  memb_and_rest  A -> (list A) -> (list A) -> o.
type  drop_l         int -> (list A) -> (list A) -> o.
type  reverse       (list A) -> (list A) -> o.

end