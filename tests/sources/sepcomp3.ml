let us = [{|

main :- p.

pred p.

:name "xxx"
p :- print "one".

|}; {|

:name "xxx"
p :- print "two".

|}; ]
;;

let () = Sepcomp.Sepcomp_template.main us;;