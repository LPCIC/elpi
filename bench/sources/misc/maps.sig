sig  maps.

kind  i  type.

type  father  i -> i -> o.

type  jane    i.
type  moses   i.
type  john    i.
type  peter   i.
type  james   i.
type  charles i.

exportdef	mapfun		list A -> (A -> B) -> list B -> o.
exportdef	mappred		list A -> (A -> B -> o) -> list B -> o.
exportdef	reduce		list A -> (A -> B -> B) -> B -> B -> o.
exportdef	reduce_eval	list A -> (A -> B -> B) -> B -> B -> o.
exportdef	reduce_pred	list A -> (A -> B -> o) -> 
                                              (B -> B -> B) -> B -> o.
exportdef	for_each	list A -> (A -> o) -> o.
