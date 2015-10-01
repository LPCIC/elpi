/*

File: pairs.sig
Author: Louise Dennis
Description: Pair type
Last Modified: 16th October 2000

*/

sig pairs.

kind   pairing       type -> type -> type.
type   @@            A -> B -> (pairing A B).
infix  @@ 100.

end