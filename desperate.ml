(* GC off
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.space_overhead = max_int;
  } in
  Gc.set tweaked_control
;;
*)

(* Invariant: a Heap term never points to a Query term *)
type term =
  (* Pure terms *)
  | Const of string
  (* Query terms *)
  | Struct of term array
  | Arg of int
  (* Heap terms *)
  | App of term array
  | UVar of term array * int (* and eventually extra metadata like the level *)

(* A term cannot be just UVar,  if so it is a degenerate App [| UVar(..) |] *)

let ppterm f t =
  let rec ppapp a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    let last = Array.length a - 1 in
    Array.iteri (fun j x -> aux a x; if j <> last then Format.fprintf f "@ ") a;
    Format.fprintf f "@]%c" c2
  and aux a = function
    | App a -> ppapp a '(' ')'
    | Struct a -> ppapp a '{' '}'
    | UVar (a',i) ->
         if a' == a then Format.fprintf f "(%d)" i
         else Format.fprintf f "%d+%d" (Obj.magic a') i
    | Const s -> Format.fprintf f "%s" s
    | Arg i -> Format.fprintf f "A%d" i
  in
    aux [||] t
;;

let undef a i = match a.(i) with UVar(b,j) -> b == a && i == j | _ -> false

let dummyk = "dummy"

let key_of = function
  | (App xs | Struct xs) -> begin
      match xs.(0), xs.(1) with
      | Const w, (App ys | Struct ys) -> begin
          match ys.(0) with
          | Const z -> w,z
          | _ -> w, dummyk
          end
      | Const w, Const z -> w,z
      | Const w, _ -> w,dummyk
      | _ -> dummyk, dummyk
  end
  | _ -> dummyk, dummyk

type key = string * string

type clause = { hd : term; hyps : term list; vars : int; key : key }

let clause_match_key (j1,j2) { key = (k1,k2) } =
  j1 == dummyk || k1 == dummyk ||
  (j1 == k1 && (j2 == dummyk || k2 == dummyk || j2 == k2))

(* The environment of a clause and stack frame *)

let mk_env size =
  let a = Array.make size (Arg (-1)) in
  Array.iteri (fun i _ -> a.(i) <- UVar (a,i)) a;
  a

let to_heap e t =
  let rec every = function
    | [] -> ()
    | t :: ts -> every (each t ts)
  and each a todo =
    let len = Array.length a in
    let todo = ref todo in
    for j = 0 to len - 1 do
      match a.(j) with
      | (Const _ | UVar _ | App _) -> ()
      | Struct b ->
          let c = Array.copy b in
          todo := c :: !todo;
          a.(j) <- App c 
      | Arg i when undef e i ->
          let v = UVar(a,j) in
          a.(j) <- v;
          e.(i) <- v
      | Arg i ->
          match e.(i) with
          | (Const _ | UVar _ | App _) as x -> a.(j) <- x
          | Struct b ->
               let c = Array.copy b in
               todo := c :: !todo;
               let v = App c in
               a.(j) <- v;
               e.(i) <- v
          | Arg _ -> assert false
    done;
    !todo in
  let res = [|t|] in
  every [res];
  res.(0)
;;

type frame = {
  env : term array;
  lvl : int;
  goals : (key * term) list;
  next : frame;
}

let mk_frame stack_top (c : clause) = {
  env = mk_env c.vars;
  lvl = 1 + stack_top.lvl;
  goals = List.map (fun x -> (dummyk,dummyk), x) c.hyps;
  next = stack_top;
}

(* Unification *)

let trail_this (trail,no_alternative) old =
  match no_alternative with
  | true -> ()
  | false -> trail := old :: !trail

(* Invariant: LSH is a heap term *)
let unif trail e_a e_b a b =
 let rec unif a b todo =
   (* Format.eprintf "unif: %a = %a\n%!" ppterm a ppterm b; *)
   a == b || match a,b with
   | (Arg _ | Struct _), _ -> assert false
   | _, Arg i when not (undef e_b i) -> unif a e_b.(i) todo
   | UVar(a,i), _ when not (undef a i) -> unif a.(i) b todo
   | _, UVar(b,i) when not (undef b i) -> unif a b.(i) todo
   | UVar _, Arg j -> e_b.(j) <- a; true
   | t, Arg i -> trail_this trail e_b.(i); e_b.(i) <- t; true
   | UVar(a,n) as old, t -> trail_this trail old; a.(n) <- to_heap e_b t; true
   | t, (UVar(a,n) as old) -> trail_this trail old; a.(n) <- t; true
   | Const x, Const y -> x == y (* !!! hashcons the entire Const node *)
   | App xs, (Struct ys | App ys) -> todo := (xs,ys) :: !todo; true
   | Const _, (App _ | Struct _) -> false
   | App _, Const _  -> false in
 let todo = ref [] in
 let b = ref (unif a b todo) in
 let more = ref (!todo != []) in
 while !b && !more do
   match !todo with
   | [] -> more := false
   | (xs, ys) :: rest ->
      todo := rest;
      let len = Array.length xs in
      b := len = Array.length ys;
      let i = ref 0 in
      while !b && !i < len do
        let cur = !i in
        b := unif xs.(cur) ys.(cur) todo;
        incr i;
      done;
 done;
 !b
;;

(* Backtracking *)

type alternative = {
  stack : frame;
  trail : term list;
  clauses : clause list
}

let undo_trail old_trail trail =
  while !trail != old_trail do
    match !trail with
    | UVar(a,i) :: rest -> a.(i) <- UVar(a,i); trail := rest
    | _ -> assert false
  done
;;

let put_all_args f = { f with
   goals = List.map (fun (_,x) ->
     let x = to_heap f.env x in
     key_of x, x)
   f.goals
}

let run1 trail e_g g c stack last_call =
  let old_trail = !trail in
  let f = mk_frame stack c in
  if unif (trail,last_call) e_g f.env g c.hd
  then Some (put_all_args f)
  else (undo_trail old_trail trail; None)
;;

let rec select trail e_g g stack p old_stack alts =
  match p with
  | [] -> None
  | c :: cs ->
     let old_trail = !trail in
     match run1 trail e_g g c stack (alts = []) with
     | None -> select trail e_g g stack cs old_stack alts
     | Some new_stack ->
         Some (new_stack, (* crucial *)
               if cs = [] then alts
               else { stack = old_stack; trail = old_trail; clauses = cs }
                    :: alts)
;;

let filter cl k = List.filter (clause_match_key k) cl

let set_goals s gs = { s with goals = gs }

let rec run p cp trail (stack : frame) alts =
  match stack.goals with
  | [] ->
      if stack.lvl == 0 then () else run p p trail stack.next alts
  | (key_g,g) :: gs ->
      let cp = filter cp key_g in
      match select trail stack.env g (set_goals stack gs) cp stack alts with
      | Some (stack, alts) -> run p p trail stack alts
      | None ->
          match alts with
          | [] -> raise (Failure "no clause")
          | { stack; trail = old_trail; clauses } :: alts ->
              undo_trail old_trail trail;
              run p clauses trail stack alts
;;
let run p s = run p p (ref []) s []
  

(* Test *)

(* Hashconsed constants *)
let appk = "app"
let nilk = "nil"
let revk = "rev"
let eqk = "eq"
let consk = "cons"
let ak = "a"
let bk = "b"

(* Program *)
let app1 = { hd = Struct[| Const appk; Const nilk; Arg 0; Arg 0 |]; hyps = []; vars = 1; key = (appk,nilk) };;
let app2 = { hd = Struct[| Const appk; Struct[|Const consk; Arg 0; Arg 1|]; Arg 2; Struct [|Const consk; Arg 0; Arg 3 |] |]; hyps = [ Struct [| Const appk; Arg 1; Arg 2; Arg 3|] ]; vars = 4; key = (appk,consk) };;

let rev1 = { hd = Struct[| Const revk; Const nilk; Arg 0; Arg 0 |]; hyps = []; vars = 1; key = (revk,nilk) };;
let rev2 = { hd = Struct[| Const revk; Struct[| Const consk; Arg 0; Arg 1|]; Arg 2; Arg 3 |];
             hyps = [Struct[|Const revk; Arg 1; Struct [| Const consk; Arg 0; Arg 2|]; Arg 3|]];
             vars = 4; key = (revk,consk) };;
let refl = { hd = Struct[| Const eqk; Arg 0; Arg 0|]; hyps = []; vars = 1; key = (eqk,dummyk) };;

(*
let l1 =
   App [| Const consk; Const ak; App [| Const consk; Const bk; Const nilk |]|];; 
let gs =
  let rec a1 = [|Const appk; l1; l1; UVar(a1,3)|] in
  let rec aR1 = [|Const revk; UVar(a1,3); Constnilk; UVar(aR1,3)|] in
  let rec aR2 = [|Const revk; UVar(aR1,3); Constnilk; UVar(aR2,3)|] in
  [
          App a1;
          App aR1;
          App aR2;
          App [|Const eqk; UVar(a1,3);UVar(aR2,3)|] 
  ];;

let p = [app1;app2;rev1;rev2;refl];;
let rec top = { lvl = 0; env = [||]; goals = gs; next = top; };;
run p top ;;

exit 0;;
*)

let l1 =
   App [| Const consk; Const ak; App [| Const consk; Const bk; 
   App [| Const consk; Const ak; App [| Const consk; Const bk; 
   App [| Const consk; Const ak; App [| Const consk; Const bk; 
   App [| Const consk; Const ak; App [| Const consk; Const bk; 
   App [| Const consk; Const ak; App [| Const consk; Const bk; 
   Const nilk |]|]|]|]|]|]|]|]|]|];;
let gs =
  let rec a1 = [|Const appk; l1; l1; UVar(a1,3)|] in
  let rec a2 = [|Const appk; UVar(a1,3); UVar(a1,3); UVar(a2,3)|] in
  let rec a3 = [|Const appk; UVar(a2,3); UVar(a2,3); UVar(a3,3)|] in
  let rec a4 = [|Const appk; UVar(a3,3); UVar(a3,3); UVar(a4,3)|] in
  let rec a5 = [|Const appk; UVar(a4,3); UVar(a4,3); UVar(a5,3)|] in
  let rec a6 = [|Const appk; UVar(a5,3); UVar(a5,3); UVar(a6,3)|] in
  let rec a7 = [|Const appk; UVar(a6,3); UVar(a6,3); UVar(a7,3)|] in
  let rec a8 = [|Const appk; UVar(a7,3); UVar(a7,3); UVar(a8,3)|] in
  let rec a9 = [|Const appk; UVar(a8,3); UVar(a8,3); UVar(a9,3)|] in
  let rec a10 = [|Const appk; UVar(a9,3); UVar(a9,3); UVar(a10,3)|] in
  let rec a11 = [|Const appk; UVar(a10,3); UVar(a10,3); UVar(a11,3)|] in
  let rec a12 = [|Const appk; UVar(a11,3); UVar(a11,3); UVar(a12,3)|] in
  let rec a13 = [|Const appk; UVar(a12,3); UVar(a12,3); UVar(a13,3)|] in
  let rec a14 = [|Const appk; UVar(a13,3); UVar(a13,3); UVar(a14,3)|] in
  let rec aR1 = [|Const revk; UVar(a14,3); Const nilk; UVar(aR1,3)|] in
  let rec aR2 = [|Const revk; UVar(aR1,3); Const nilk; UVar(aR2,3)|] in
  [
          App a1;
          App a2;
          App a3;
          App a4;
          App a5;
          App a6;
          App a7;
          App a8;
          App a9;
          App a10;
          App a11;
          App a12;
          App a13;
          App a14;
          App aR1;
          App aR2;
          App [|Const eqk; UVar(a14,3);UVar(aR2,3)|] 
  ];;

let p = [app1;app2;rev1;rev2;refl];;
let rec top = { lvl = 0; env = mk_env 0; goals = List.map (fun x -> key_of x, x) gs; next = top; };;
run p top;;
