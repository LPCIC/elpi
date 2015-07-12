type t = I | K | S | App of t * t;;

let rec pp =
 function
    I -> "I"
  | K -> "K"
  | S -> "S"
  | App(t1,t2) -> "(" ^ pp t1 ^ " " ^ pp t2 ^ ")"

let app x y = App(x,y);;

let res = (app (app (app (app S S) (app I (app I S))) (app K (app (app S (app I S)) S))) (app (app K S) (app K I)))

let rec eval =
 function
    I | K | S as x -> x
  | App(m,t) ->
     let t = eval t in
     match eval m with
        I -> eval t
      | K -> App(K,t)
      | S -> App(S,t)
      | App(K,x) -> eval x
      | App(S,x) -> App(App(S,x),t)
      | App(App(S,x),y) -> eval (App (App(x,t), App(y,t)))
      | _ -> assert false
;;

prerr_endline (pp (eval res))
