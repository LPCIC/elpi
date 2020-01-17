let us = [{|

type x int.
type y int.
main :- p x.

|}; {|

type y int.
type x int.

pred p i:int.

p x :- print "ok".
p _ :- print "ko".

|}; ]
;;

let () = Sepcomp.Sepcomp_template.main us;;