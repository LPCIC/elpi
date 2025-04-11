let us = [{|

main :- p 1.

pred p o:int.

|}; {|

pred p i:int.

p X :- print X.

|}; ]
;;

let () = Sepcomp.Sepcomp_template.main us;;