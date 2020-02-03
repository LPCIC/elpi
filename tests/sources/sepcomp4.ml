let us = [{|

main :- p 1.

pred p i:int.

|}; {|

pred p o:int.

p X :- print X.

|}; ]
;;

let () = Sepcomp.Sepcomp_template.main us;;