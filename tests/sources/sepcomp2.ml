let us = [{|

pred p.
main :- p.

|}; {|

pred p.
p :- print "ok".

|}; ]
;;

let () = Sepcomp.Sepcomp_template.main us;;