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
  | Struct of term * term * term list
  | Arg of int
  (* Heap terms *)
  | App of term * term * term list
  | UVar of term ref

let rec dummy = App (dummy,dummy,[])

let ppterm f t =
  let rec ppapp a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    List.iter (fun x -> aux x; Format.fprintf f "@ ") a;
    Format.fprintf f "@]%c" c2
  and aux = function
    | App (hd,x,xs)-> ppapp (hd::x::xs) '(' ')'
    | Struct (hd,x,xs) -> ppapp (hd::x::xs) '{' '}'
    | UVar { contents = t } -> aux t
    | Const s -> Format.fprintf f "%s" s
    | Arg i -> Format.fprintf f "A%d" i
  in
    aux t
;;

type key = string * string

type clause = { hd : term; hyps : term list; vars : int; key : key }

let dummyk = "dummy"

let key_of = function
  | (App (Const w,Const z, _) | Struct (Const w,Const z, _)) -> w, z
  | (App (Const w,App(Const z,_,_), _) | Struct (Const w,App(Const z,_,_), _)) -> w, z
  | (App (Const w,_, _) | Struct (Const w,_, _)) -> w, dummyk
  | _ -> dummyk, dummyk

let clause_match_key (j1,j2) { key = (k1,k2) } =
  j1 == dummyk || k1 == dummyk ||
  (j1 == k1 && (j2 == dummyk || k2 == dummyk || j2 == k2))

(* The environment of a clause and stack frame *)

let mk_env size = Array.create size dummy

let trail_this (trail,no_alternative) old =
  match no_alternative with
  | true -> ()
  | false -> trail := old :: !trail

let to_heap trail e t =
  let rec aux = function
    | (Const _ | UVar _ | App _) as x -> x (* heap term *)
    | Struct(hd,b,bs) -> App (aux hd, aux b, List.map aux bs)
    | Arg i ->
        let a = e.(i) in
        if a == dummy then
            let v = UVar(ref dummy) in
            trail_this trail (`Arr(e,i));
            e.(i) <- v;
            v
        else aux a
  in aux t
;;

type frame = {
  env : term array;
  lvl : int;
  goals : term list;
  next : frame;
}

let mk_frame stack_top (c : clause) = {
  env = mk_env c.vars;
  lvl = 1 + stack_top.lvl;
  goals = c.hyps;
  next = stack_top;
}

(* Unification *)

(* Invariant: LSH is a heap term *)
let unif trail e_b a b =
 let rec unif a b =
   (* Format.eprintf "unif: %a = %a\n%!" ppterm a ppterm b; *)
   a == b || match a,b with
   | (Arg _ | Struct _), _ -> assert false
   | _, Arg i when e_b.(i) != dummy -> unif a e_b.(i)
   | UVar { contents = t }, _ when t != dummy -> unif t b
   | _, UVar { contents = t } when t != dummy -> unif a t
   | UVar _, Arg j -> e_b.(j) <- a; true
   | t, Arg i -> trail_this trail (`Arr (e_b,i)); e_b.(i) <- t; true
   | UVar r, t -> trail_this trail (`Ref r); r := to_heap trail e_b t; true
   | t, UVar r -> trail_this trail (`Ref r); r := t; true
   | Const x, Const y -> x == y (* !!! hashcons the entire Const node *)
   | App (x1,x2,xs), (Struct (y1,y2,ys) | App (y1,y2,ys)) ->
       unif x1 y1 && unif x2 y2 && List.for_all2 unif xs ys
   | Const _, (App _ | Struct _) -> false
   | App _, Const _  -> false in
 unif a b
;;

(* Backtracking *)

type trail = [ `Arr of term array * int | `Ref of term ref ]

type alternative = {
  stack : frame;
  trail : trail list;
  clauses : clause list
}

let undo_trail old_trail trail =
  while !trail != old_trail do
    match !trail with
    | `Ref r :: rest -> r := dummy; trail := rest
    | `Arr(a,i) :: rest -> a.(i) <- dummy; trail := rest
    | _ -> assert false
  done
;;

(* Loop *)

let run1 trail g c stack last_call =
  let old_trail = !trail in
  let f = mk_frame stack c in
  if unif (trail,last_call) f.env g c.hd
  then Some f
  else (undo_trail old_trail trail; None)
;;

let rec select trail g stack p old_stack alts =
  match p with
  | [] -> None
  | c :: cs ->
     let old_trail = !trail in
     match run1 trail g c stack (alts = []) with
     | None -> select trail g stack cs old_stack alts
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
  | g :: gs ->
      let g = to_heap (trail,alts=[]) stack.env g in (* put args *)
      let cp = filter cp (key_of g) in
      match select trail g (set_goals stack gs) cp stack alts with
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

let cak = Const ak
let cbk = Const bk
let cconsk = Const consk
let cnilk = Const nilk
let cappk = Const appk
let crevk = Const revk

(* Program *)
let app1 = { hd = Struct (cappk, cnilk, [Arg 0; Arg 0 ]); hyps = []; vars = 1; key = (appk,nilk) };;
let app2 = { hd = Struct (cappk, Struct(cconsk, Arg 0, [Arg 1]), [Arg 2; Struct (cconsk, Arg 0, [Arg 3 ]) ]); hyps = [ Struct (cappk, Arg 1, [Arg 2; Arg 3]) ]; vars = 4; key = (appk,consk) };;

let rev1 = { hd = Struct( crevk, cnilk, [Arg 0; Arg 0 ]); hyps = []; vars = 1; key = (revk,nilk) };;
let rev2 = { hd = Struct( crevk, Struct(cconsk, Arg 0, [Arg 1]), [Arg 2; Arg 3 ]);
             hyps = [Struct(crevk, Arg 1, [Struct ( cconsk, Arg 0, [Arg 2]); Arg 3])];
             vars = 4; key = (revk,consk) };;
let refl = { hd = Struct(Const eqk, Arg 0, [Arg 0]); hyps = []; vars = 1; key = (eqk,dummyk) };;

let l1 =
   App (cconsk, cak, [App (cconsk, cbk, [ 
   App (cconsk, cak, [App (cconsk, cbk, [ 
   App (cconsk, cak, [App (cconsk, cbk, [ 
   App (cconsk, cak, [App (cconsk, cbk, [ 
   App (cconsk, cak, [App (cconsk, cbk, [ 
   cnilk ])])])])])])])])])]);;
let gs =
  let v1 = UVar (ref dummy) in
  let v2 = UVar (ref dummy) in
  let v3 = UVar (ref dummy) in
  let v4 = UVar (ref dummy) in
  let v5 = UVar (ref dummy) in
  let v6 = UVar (ref dummy) in
  let v7 = UVar (ref dummy) in
  let v8 = UVar (ref dummy) in
  let v9 = UVar (ref dummy) in
  let v10 = UVar (ref dummy) in
  let v11 = UVar (ref dummy) in
  let v12 = UVar (ref dummy) in
  let v13 = UVar (ref dummy) in
  let v14 = UVar (ref dummy) in
  let r1 = UVar (ref dummy) in
  let r2 = UVar (ref dummy) in
  let a1 = App (cappk, l1, [ l1; v1] ) in
  let a2 = App (cappk, v1, [ v1; v2] ) in
  let a3 = App (cappk, v2, [ v2; v3] ) in
  let a4 = App (cappk, v3, [ v3; v4] ) in
  let a5 = App (cappk, v4, [ v4; v5] ) in
  let a6 = App (cappk, v5, [ v5; v6] ) in
  let a7 = App (cappk, v6, [ v6; v7] ) in
  let a8 = App (cappk, v7, [ v7; v8] ) in
  let a9 = App (cappk, v8, [v8; v9] ) in
  let a10 = App (cappk, v9, [v9; v10] ) in
  let a11 = App (cappk, v10, [ v10; v11] ) in
  let a12 = App (cappk, v11, [ v11; v12] ) in
  let a13 = App (cappk, v12, [ v12; v13] ) in
  let a14 = App (cappk, v13, [ v13; v14] ) in
  let aR1 = App (crevk, v14, [ cnilk; r1] ) in
  let aR2 = App (crevk, r1, [cnilk; r2] ) in
  [
          a1;
          a2;
          a3;
          a4;
          a5;
          a6;
          a7;
          a8;
          a9;
          a10;
          a11;
          a12;
          a13;
          a14;
          aR1;
          aR2;
          App (Const eqk, v14, [r2]) 
  ];;

let p = [app1;app2;rev1;rev2;refl];;
let rec top = { lvl = 0; env = mk_env 0; goals = gs; next = top; };;
run p top;;
