(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type Show = sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

module type Show1 = sig
  type 'a t
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
end

module Map = struct

  module type S = sig
    include Map.S
    include Show1 with type 'a t := 'a t
  end
  
  module type OrderedType = sig
    include Map.OrderedType
    include Show with type t := t
  end

  module Make (Ord : OrderedType) = struct
    include Map.Make(Ord)
    let pp f fmt m =
      Format.fprintf fmt "{{ @[<hov 2>";
      iter (fun k v -> Format.fprintf fmt "%a ->@ %a;@ " Ord.pp k f v) m;
      Format.fprintf fmt "@] }}"
    let show f m =
      let b = Buffer.create 20 in
      let fmt = Format.formatter_of_buffer b in
      pp f fmt m;
      Format.fprintf fmt "@?";
      Buffer.contents b
  end

end

module Set = struct

  module type S = sig
    include Set.S
    include Show with type t := t
  end
  
  module type OrderedType = sig
    include Set.OrderedType
    include Show with type t := t
  end

  module Make (Ord : OrderedType) = struct
    include Set.Make(Ord)
    let pp fmt m =
      Format.fprintf fmt "{{ @[<hov 2>";
      iter (fun x -> Format.fprintf fmt "%a;@ " Ord.pp x) m;
      Format.fprintf fmt "@] }}"
    let show m =
      let b = Buffer.create 20 in
      let fmt = Format.formatter_of_buffer b in
      pp fmt m;
      Format.fprintf fmt "@?";
      Buffer.contents b
  end

end

module Int = struct
  type t = int [@@deriving show]
  let compare x y = x - y
end

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show x = x
end

module IntMap = Map.Make(Int)
module StrMap = Map.Make(String)
module IntSet = Set.Make(Int)
module StrSet = Set.Make(String)
module Fmt = Format

module Loc = struct
  type t = {
    source_name : string;
    source_start: int;
    source_stop: int;
    line: int;
    line_starts_at: int;
  }
  [@@deriving eq, ord]

  let to_string {
    source_name;
    source_start;
    source_stop;
    line;
    line_starts_at; }
  =
    let source =
     if source_name = "" then ""
     else source_name ^ ", " in
    let chars = Printf.sprintf "characters %d-%d" source_start source_stop in
    let pos =
      if line = -1 then chars
      else Printf.sprintf "%s, line %d, column %d"
             chars line (source_stop - line_starts_at) in
    source ^ pos

  let pp fmt l = Fmt.fprintf fmt "%s" (to_string l)
  let show l = to_string l

  let initial source_name = {
    source_name;
    source_start = 0;
    source_stop = 0;
    line = 1;
    line_starts_at = 0;
  }

end

let pplist ?(max=max_int) ?(boxed=false) ppelem ?(pplastelem=ppelem) sep f l =
 if l <> [] then begin
  if boxed then Fmt.fprintf f "@[<hov>";
  let args,last = match List.rev l with
    [] -> assert false;
  | head::tail -> List.rev tail,head in
  List.iteri (fun i x -> if i = max + 1 then Fmt.fprintf f "..."
                         else if i > max then ()
                         else Fmt.fprintf f "%a%s@," ppelem x sep) args;
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

let rec uniqq =
 function
    [] -> []
  | x::xs when List.memq x xs -> uniqq xs
  | x::xs -> x::uniqq xs
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

let pp_loc_opt = function
  | None -> ""
  | Some loc -> Loc.show loc ^ ": "
let default_warn ?loc s =
  Printf.eprintf "Warning: %s%s\n%!" (pp_loc_opt loc) s
let default_error ?loc s =
  Printf.eprintf "Fatal error: %s%s\n%!" (pp_loc_opt loc) s;
  exit 1
let default_anomaly ?loc s =
  Printf.eprintf "Anomaly: %s%s\n%!" (pp_loc_opt loc) s;
  exit 2
let default_type_error ?loc s = default_error ?loc s
let default_printf = Printf.printf
let default_eprintf = Printf.eprintf

let warn_f       = ref (Obj.repr default_warn)
let error_f      = ref (Obj.repr default_error)
let anomaly_f    = ref (Obj.repr default_anomaly)
let type_error_f = ref (Obj.repr default_type_error)
let std_fmt      = ref Format.std_formatter
let err_fmt      = ref Format.err_formatter

let set_formatters_maxcols i =
  Format.pp_set_margin !std_fmt i;
  Format.pp_set_margin !err_fmt i
let set_formatters_maxbox i =
  Format.pp_set_max_boxes !std_fmt i;
  Format.pp_set_max_boxes !err_fmt i

let set_warn f       = warn_f       := (Obj.repr f)
let set_error f      = error_f      := (Obj.repr f)
let set_anomaly f    = anomaly_f    := (Obj.repr f)
let set_type_error f = type_error_f := (Obj.repr f)
let set_std_formatter f = std_fmt := f
let set_err_formatter f = err_fmt := f

let warn ?loc s       = Obj.obj !warn_f ?loc s
let error ?loc s      = Obj.obj !error_f ?loc s
let anomaly ?loc s    = Obj.obj !anomaly_f ?loc s
let type_error ?loc s = Obj.obj !type_error_f ?loc s
let printf x     = Format.fprintf !std_fmt x
let eprintf x    = Format.fprintf !err_fmt x

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
module Pair = struct
  type ('a,'b) t = 'a * 'b [@@deriving show]
end
let pp_option = Option.pp
let pp_int = Int.pp
let pp_string = String.pp
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

let map_acc2 f acc l1 l2 =
  let a, l =
    List.fold_left2 (fun (a,xs) x y -> let a, x = f a x y in a, x :: xs)
      (acc, []) l1 l2 in
  a, List.rev l

let map_acc3 f acc l1 l2 l3 =
  let rec aux a l l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> a, List.rev l
    | x::xs, y::ys, z::zs ->
        let a, v = f a x y z in
        aux a (v::l) xs ys zs
    | _ -> invalid_arg "map_acc3"
  in
    aux acc [] l1 l2 l3

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
(*       [%spy "exec-begin" (fun _ _ -> ()) ()]; *)
      Global.restore !my_globals;
      try
       let rc = f x in
       my_globals := Global.backup ();
       Global.restore saved_globals;
(*        [%spy "exec-end" (fun _ _ -> ()) ()]; *)
       rc
      with e ->
       my_globals := Global.backup ();
       Global.restore saved_globals;
(*        [%spy "exec-end" (fun _ _ -> ()) ()]; *)
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
  type tt = t

  type 'a data_declaration = {
    data_name : string;
    data_pp : Format.formatter -> 'a -> unit;
    data_eq : 'a -> 'a -> bool;
    data_hash : 'a -> int;
    data_hconsed : bool;
  }

  type 'a cdata = { cin : 'a -> t; isc : t -> bool; cout: t -> 'a; name : string }
  
  type cdata_declaration = {
    cdata_name : string;
    cdata_pp : Format.formatter -> t -> unit;
    cdata_eq : t -> t -> bool;
    cdata_hash : t -> int;
    cdata_canon : t -> t;
  }

let m : cdata_declaration IntMap.t ref = ref IntMap.empty

let cget x = Obj.obj x.t
let pp f x = (IntMap.find x.ty !m).cdata_pp f x
let equal x y = x.ty = y.ty && (IntMap.find x.ty !m).cdata_eq x y
let hash x = (IntMap.find x.ty !m).cdata_hash x
let name x = (IntMap.find x.ty !m).cdata_name
let hcons x = (IntMap.find x.ty !m).cdata_canon x
let ty2 { isc } ({ ty = t1 } as x) { ty = t2 } = isc x && t1 = t2
let show x =
  let b = Buffer.create 22 in
  Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" pp x;
  Buffer.contents b

let fresh_tid =
  let tid = ref 0 in
  fun () -> incr tid; !tid

let declare { data_eq; data_pp; data_hash; data_name; data_hconsed } =
  let tid = fresh_tid () in
  let cdata_eq x y = data_eq (cget x) (cget y) in
  let cdata_hash x = data_hash (cget x) in
  let cdata_canon =
    if data_hconsed then
      let module CD : Hashtbl.HashedType with type t = tt = struct
        type t = tt
        let hash = cdata_hash
        let equal = cdata_eq
      end in
      let module HS : Weak.S with type data = tt = Weak.Make(CD) in
      let h = HS.create 17 in
      (fun x -> try HS.find h x
                with Not_found -> HS.add h x; x)
    else (fun x -> x) in
  let cdata_eq_hconsed =
    if data_hconsed then (fun x y -> cget x == cget y)
    else cdata_eq in
  m := IntMap.add tid { cdata_name = data_name;
                   cdata_pp = (fun f x -> data_pp f (cget x));
                   cdata_eq = cdata_eq_hconsed;
                   cdata_hash;
                   cdata_canon;
       } !m;
  {
    cin = (fun v -> cdata_canon { t = Obj.repr v; ty = tid });
    isc = (fun c -> c.ty = tid);
    cout = (fun c -> assert(c.ty = tid); cget c);
    name = data_name;
  }

  let morph1 { cin; cout } f x = cin (f (cout x))
  let morph2 { cin; cout } f x y = cin (f (cout x) (cout y))
  
  let map { cout } { cin } f x = cin (f (cout x))
end
  
module State = struct

  type t = Obj.t StrMap.t
  type 'a component = string
  type extension = {
    init : unit -> Obj.t;
    end_comp : Obj.t -> Obj.t option;
    pp   : Format.formatter -> Obj.t -> unit;
  }
  let extensions : extension StrMap.t ref = ref StrMap.empty

  let get name t =
    try Obj.obj (StrMap.find name t)
    with Not_found ->
       anomaly ("State.get: component " ^ name ^ " not found")

  let set name t v = StrMap.add name (Obj.repr v) t
  let update name t f =
    StrMap.add name (Obj.repr (f (Obj.obj (StrMap.find name t)))) t
  let update_return name t f =
    let x = get name t in
    let x, res = f x in
    let t = set name t x in
    t, res

  let declare ~name ~pp ~init ~compilation_is_over =
    if StrMap.mem name !extensions then
      anomaly ("Extension "^name^" already declared");
    extensions := StrMap.add name {
        init = (fun x -> Obj.repr (init x));
        pp = (fun fmt x -> pp fmt (Obj.obj x));
        end_comp = (fun x -> option_map Obj.repr (compilation_is_over (Obj.obj x))) }
      !extensions;
    name

  let init () =
    StrMap.fold (fun name { init } -> StrMap.add name (init ()))
      !extensions StrMap.empty 

  let end_compilation m =
    StrMap.fold (fun name obj acc -> 
      match (StrMap.find name !extensions).end_comp obj with
      | None -> acc
      | Some o -> StrMap.add name o acc) m StrMap.empty

  let pp fmt t =
    StrMap.iter (fun name { pp } ->
      try pp fmt (StrMap.find name t)
      with Not_found -> ())
    !extensions

end
