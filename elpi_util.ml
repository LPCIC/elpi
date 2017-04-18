(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Fmt = Format

let pplist ?(max=max_int) ?(boxed=false) ppelem ?(pplastelem=ppelem) sep f l =
 if l <> [] then begin
  if boxed then Fmt.fprintf f "@[<hov>";
  let args,last = match List.rev l with
    [] -> assert false;
  | head::tail -> List.rev tail,head in
  List.iteri (fun i x -> if i = max + 1 then Fmt.fprintf f "..."
                         else if i > max then ()
                         else Fmt.fprintf f "%a%s@ " ppelem x sep) args;
  Fmt.fprintf f "%a" pplastelem last;
  if boxed then Fmt.fprintf f "@]"
 end
;;

let rec smart_map f =
 function
    [] -> []
  | (hd::tl) as l ->
     let hd' = f hd in
     let tl' = smart_map f tl in
     if hd==hd' && tl==tl' then l else hd'::tl'
;;

let rec for_all3b p l1 l2 bl b =
  match (l1, l2, bl) with
  | ([], [], _) -> true
  | ([a1], [a2], []) -> p a1 a2 b
  | ([a1], [a2], b3::_) -> p a1 a2 b3
  | (a1::l1, a2::l2, []) -> p a1 a2 b && for_all3b p l1 l2 bl b
  | (a1::l1, a2::l2, b3::bl) -> p a1 a2 b3 && for_all3b p l1 l2 bl b
  | (_, _, _) -> false
;;

let rec for_all2 p l1 l2 =
  match (l1, l2) with
  | ([], []) -> true
  | ([a1], [a2]) -> p a1 a2
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> false
;;

let error s =
  Printf.eprintf "Fatal error: %s\n%!" s;
  exit 1
let anomaly s =
  Printf.eprintf "Anomaly: %s\n%!" s;
  exit 2
let type_error = error


let option_get ?err = function
  | Some x -> x
  | None ->
      match err with
      | None -> assert false
      | Some msg -> anomaly msg
let option_map f = function Some x -> Some (f x) | None -> None
let option_mapacc f acc = function
  | Some x -> let acc, y = f acc x in acc, Some y
  | None -> acc, None

module Option = struct
  type 'a t = 'a option = None | Some of 'a [@@deriving show]
end
module Int = struct
  type t = int [@@deriving show]
end
module Pair = struct
  type ('a,'b) t = 'a * 'b [@@deriving show]
end
let pp_option = Option.pp
let pp_int = Int.pp
let pp_pair = Pair.pp

let remove_from_list x =
 let rec aux acc =
  function
     [] -> anomaly "Element to be removed not in the list"
   | y::tl when x==y -> List.rev acc @ tl
   | y::tl -> aux (y::acc) tl
 in
  aux []

let rec map_exists f =
 function
    [] -> None
  | hd::tl -> match f hd with None -> map_exists f tl | res -> res

let rec map_filter f =
 function
    [] -> []
  | hd::tl -> match f hd with None -> map_filter f tl | Some res -> res :: map_filter f tl


let map_acc f acc l =
  let a, l =
    List.fold_left (fun (a,xs) x -> let a, x = f a x in a, x :: xs)
      (acc, []) l in
  a, List.rev l

let partition_i f l =
  let rec aux n a1 a2 = function
    | [] -> List.rev a1, List.rev a2
    | x :: xs ->
       if (f n x) then aux (n+1) (x::a1) a2 xs else aux (n+1) a1 (x::a2) xs
  in
    aux 0 [] [] l
;;

let fold_left2i f acc l1 l2 =
  let rec aux n acc l1 l2 = match l1, l2 with
    | [],[] -> acc
    | x :: xs, y :: ys -> aux (n+1) (f n acc x y) xs ys
    | _ -> anomaly "fold_left2i" in
  aux 0 acc l1 l2

let rec uniq = function
  | [] -> []
  | [_] as x -> x
  | x :: (y :: _ as tl) -> if x = y then uniq tl else x :: uniq tl

module Global: sig
 
   type backup

   (* Takes the initial value *)
   val new_local : 'a -> 'a ref
   val backup : unit -> backup
   val restore : backup -> unit

   (* Like doing a backup just after having created all globals *)
   val initial_backup : unit -> backup
  
   (* Hack, in case the initial value cannot be provided when the
    * global is created *) 
   val set_value : 'a ref -> 'a -> backup -> backup
   val get_value : 'a ref -> backup -> 'a

end = struct

type backup = (Obj.t ref * Obj.t) list

let all_globals : backup ref = ref []

let new_local (t : 'a) : 'a ref =
  let res = ref t in
  all_globals := Obj.magic (res,t) :: !all_globals;
  res

let set_value (g : 'a ref) (v : 'a) (l : (Obj.t ref * Obj.t) list) =
  let v = Obj.repr v in
  let g :Obj.t ref = Obj.magic g in
    List.map
      (fun (g',_ as orig) -> if g == g' then (g,v) else orig)
      l

let get_value (p : 'a ref) (l : (Obj.t ref * Obj.t) list) : 'a =
  Obj.magic (List.assq (Obj.magic p) l)

let backup () : (Obj.t ref * Obj.t) list =
  List.map (fun (o,_) -> o,!o) !all_globals

let restore l = List.iter (fun (r,v) -> r := v) l

let initial_backup () = !all_globals

end

module Fork = struct
  type 'a local_ref = 'a ref

  type process = {
    exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;
    get : 'a. 'a local_ref -> 'a;
    set : 'a. 'a local_ref -> 'a -> unit
  }
    
  let new_local = Global.new_local
  let fork () =
    let saved_globals = Global.backup () in 
    let my_globals = ref (Global.initial_backup ()) in
    let ensure_runtime f x =
      [%spy "exec-begin" (fun _ _ -> ()) ()];
      Global.restore !my_globals;
      try
       let rc = f x in
       my_globals := Global.backup ();
       Global.restore saved_globals;
       [%spy "exec-end" (fun _ _ -> ()) ()];
       rc
      with e ->
       my_globals := Global.backup ();
       Global.restore saved_globals;
       [%spy "exec-end" (fun _ _ -> ()) ()];
       raise e in
    { exec = ensure_runtime;
      get = (fun p -> Global.get_value p !my_globals);
      set = (fun p v -> my_globals := Global.set_value p v !my_globals) }
          
end

module UUID = struct
 module Self = struct
   type t = int [@@ deriving show, eq, ord]
   let hash x = x
 end

 let counter = ref 0
 let make () = incr counter; !counter

 module Htbl = Hashtbl.Make(Self)

 include Self
end        

type 'a extensible_printer =
  (Format.formatter -> 'a -> [`Printed | `Passed]) ref
let mk_extensible_printer () =
  ref (fun fmt _ -> Fmt.fprintf fmt "please extend this printer"; `Printed)
let extend_printer r f =
  let g = !r in
  r := (fun fmt x ->
          match f fmt x with
          | `Printed -> `Printed
          | `Passed -> g fmt x)

let pp_extensible r fmt x =
  match !r fmt x with
  | `Printed -> ()
  | `Passed -> assert false
let pp_extensible_any r ~id fmt x =
  match !r fmt (id,Obj.repr x) with
  | `Printed -> ()
  | `Passed -> assert false

module CData = struct
  type t = {
    t : Obj.t;
    ty : int;
  }

  type 'a data_declaration = {
    data_name : string;
    data_pp : Format.formatter -> 'a -> unit;
    data_eq : 'a -> 'a -> bool;
    data_hash : 'a -> int;
  }

  type 'a cdata = { cin : 'a -> t; isc : t -> bool; cout: t -> 'a }

module M = Map.Make(struct type t = int let compare x y = x - y end)
let m : t data_declaration M.t ref = ref M.empty

let cget x = Obj.obj x.t
let pp f x = (M.find x.ty !m).data_pp f x
let equal x y = x.ty = y.ty && (M.find x.ty !m).data_eq x y
let hash x = (M.find x.ty !m).data_hash x
let name x = (M.find x.ty !m).data_name
let ty2 { isc } ({ ty = t1 } as x) { ty = t2 } = isc x && t1 = t2
let show x =
  let b = Buffer.create 22 in
  Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" pp x;
  Buffer.contents b

let fresh_tid =
  let tid = ref 0 in
  fun () -> incr tid; !tid

let declare { data_eq; data_pp; data_hash; data_name } =
  let tid = fresh_tid () in
  m := M.add tid { data_name;
                   data_pp = (fun f x -> data_pp f (cget x));
                   data_eq = (fun x y -> data_eq (cget x) (cget y));
                   data_hash = (fun x -> data_hash (cget x));
       } !m;
  { cin = (fun v -> { t = Obj.repr v; ty = tid });
    isc = (fun c -> c.ty = tid);
    cout = (fun c -> assert(c.ty = tid); cget c) }

  let morph1 { cin; cout } f x = cin (f (cout x))
  let morph2 { cin; cout } f x y = cin (f (cout x) (cout y))
  
  let map { cout } { cin } f x = cin (f (cout x))
end
  
module ExtState = struct
  module SM = Map.Make(String)

  type t = Obj.t SM.t
  type 'a set = t -> 'a -> t
  type 'a update = t -> ('a -> 'a) -> t
  type 'a get = t -> 'a
  type 'a init = unit -> 'a

  let get name t =
    try Obj.obj (SM.find name t)
    with Not_found -> assert false

  let set name t v = SM.add name (Obj.repr v) t
  let update name t f = SM.add name (Obj.repr (f (Obj.obj (SM.find name t)))) t

  let extensions = ref []

  let declare_extension name init =
    if List.mem_assoc name !extensions then
      anomaly ("Extension "^name^" already declared");
    extensions := (name,fun () -> Obj.repr (init ())) :: !extensions;
    get name, set name, update name

  let init () =
    List.fold_right
      (fun (name,f) -> SM.add name (f ()))
      !extensions SM.empty 

end
