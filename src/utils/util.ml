(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type Show = sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

module type ShowKey = sig
  type key
  val pp_key : Format.formatter -> key -> unit
  val show_key : key -> string
end

module type Show1 = sig
  type 'a t
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
end

module type Show2 = sig
  type ('a,'b) t
  val pp : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a,'b) t -> unit
  val show : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> ('a,'b) t -> string
end

module Map = struct

  module type S = sig
    include Map.S
    include Show1 with type 'a t := 'a t
    include ShowKey with type key := key
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

    let pp_key = Ord.pp
    let show_key = Ord.show 
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
  type t = int
  let pp fmt x = Format.pp_print_int fmt x
  let show x = Format.asprintf "@[%a@]" pp x
  let compare x y = x - y
end

module Bool = struct
  type t = bool
  let pp fmt x = Format.pp_print_bool fmt x
  let show x = Format.asprintf "@[%a@]" pp x
  let compare = Bool.compare
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

module Digest = struct
  include Digest
  let show = Digest.to_hex
  let pp fmt d = Fmt.fprintf fmt "%s" (show d)
end

module Hashtbl = struct
  include Hashtbl
  let pp pa pb fmt h =
   Format.fprintf fmt "{{ @[<hov 2>";
   Hashtbl.iter (fun k v -> Format.fprintf fmt "%a -> %a;@ " pa k pb v) h;
   Format.fprintf fmt "@] }}"
  let show pa pb h =
    let b = Buffer.create 20 in
    let fmt = Format.formatter_of_buffer b in
    pp pa pb fmt h;
    Format.fprintf fmt "@?";
    Buffer.contents b
end

module Loc = struct
  type t = {
    client_payload : Obj.t option;
    source_name : string;
    source_start: int;
    source_stop: int;
    line: int;
    line_starts_at: int;
  }

  let to_string {
    source_name;
    source_start;
    source_stop;
    line;
    line_starts_at; }
  =
    let source =
     if source_name = "" then ""
     else "File \"" ^ source_name ^ "\", " in
    let chars = Printf.sprintf "characters %d-%d" source_start source_stop in
    let pos =
      if line = -1 then chars
      else Printf.sprintf "line %d, column %d, %s"
             line (source_start - line_starts_at) chars in
    Re.(Str.global_replace (Str.regexp_string "\\") "/" source) ^ pos ^ ":"

  let pp fmt l =Fmt.fprintf fmt "%s" (to_string l)
  let show l = to_string l
  let compare = Stdlib.compare
  let equal = (=)

  let initial ?client_payload source_name = {
    client_payload;
    source_name;
    source_start = 0;
    source_stop = 0;
    line = 1;
    line_starts_at = 0;
  }
  let is_initial { source_start; source_stop; line; line_starts_at } =
    source_start = 0 && source_stop = 0 &&
    line = 1 && line_starts_at = 0

  let option_append o1 o2 =
    match o1 with
    | None -> o2
    | Some _ -> o1

  let merge ?(merge_payload=option_append) l r =
    {
    client_payload = merge_payload l.client_payload r.client_payload;
    source_name = l.source_name;
    source_start = l.source_start;
    source_stop = r.source_stop;
    line = r.line;
    line_starts_at = r.line_starts_at;
  }


  let merge ?merge_payload l r =
    if is_initial l then r
    else if is_initial r then l
    else merge ?merge_payload l r

  let extend n l = { l with source_start = l.source_start - n; source_stop = l.source_stop + n }
   
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
let rec smart_map2 f x =
  function
     [] -> []
   | (hd::tl) as l ->
      let hd' = f x hd in
      let tl' = smart_map2 f x tl in
      if hd==hd' && tl==tl' then l else hd'::tl'
 ;;
 let rec smart_map3 f x y =
  function
     [] -> []
   | (hd::tl) as l ->
      let hd' = f x y hd in
      let tl' = smart_map3 f x y tl in
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

type arg_mode = Input | Output
[@@deriving show, ord]

type mode_aux =
  | Fo of arg_mode
  | Ho of arg_mode * mode
and mode = mode_aux list
[@@deriving show, ord]

let get_arg_mode = function Fo a -> a | Ho (a,_) -> a 

let rec for_all3b3 ~argsdepth (p : argsdepth:int -> matching:bool -> 'a) x1 x2 x3 l1 l2 bl b =
  match (l1, l2, bl) with
  | ([], [], _) -> true
  | ([a1], [a2], []) -> p ~argsdepth x1 x2 x3 a1 a2 ~matching:b
  | ([a1], [a2], b3::_) -> p ~argsdepth x1 x2 x3 a1 a2 ~matching:(get_arg_mode b3 == Input)
  | (a1::l1, a2::l2, []) -> p ~argsdepth x1 x2 x3 a1 a2 ~matching:b && for_all3b3 ~argsdepth p x1 x2 x3 l1 l2 bl b
  | (a1::l1, a2::l2, b3::bl) -> p ~argsdepth x1 x2 x3 a1 a2 ~matching:(get_arg_mode b3 == Input) && for_all3b3 ~argsdepth p x1 x2 x3 l1 l2 bl b
  | (_, _, _) -> false
;;

let rec for_all2 p l1 l2 =
  match (l1, l2) with
  | ([], []) -> true
  | ([a1], [a2]) -> p a1 a2
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> false
;;
let rec for_all23 ~argsdepth (p : argsdepth:int -> matching:bool -> 'a) x1 x2 x3 l1 l2 =
  match (l1, l2) with
  | ([], []) -> true
  | ([a1], [a2]) -> p ~argsdepth x1 x2 x3 a1 a2 ~matching:false
  | (a1::l1, a2::l2) -> p ~argsdepth x1 x2 x3 a1 a2 ~matching:false && for_all23 ~argsdepth p x1 x2 x3 l1 l2
  | (_, _) -> false
;;

let pp_loc_opt = function
  | None -> ""
  | Some loc -> Loc.show loc
let default_warn ?loc s =
  Format.eprintf "@[<hv>Warning: %s@,%s@]\n%!" (pp_loc_opt loc) s
let default_error ?loc s =
  Format.eprintf "@[<hv>Fatal error: %s@,%s@]\n%!" (pp_loc_opt loc) s;
  exit 1
let default_anomaly ?loc s =
  let trace =
    match Printexc.(get_callstack max_int |> backtrace_slots) with
    | None -> ""
    | Some slots ->
        let lines = Array.mapi Printexc.Slot.format slots in
        let _, lines_repetitions =
          List.fold_left (fun (pos,acc) l ->
            match l with
            | None -> pos+1, acc
            | Some _ when pos = 0 -> pos+1, acc
            | Some l ->
                match acc with
                | (l1,q) :: acc when l = l1 -> pos+1, (l1,q+1) :: acc
                | _ -> pos+1, (l,1) :: acc)
            (0,[]) (Array.to_list lines) in
        let lines =
          lines_repetitions |> List.map (function
            | (l,1) -> l
            | (l,n) -> l ^ Printf.sprintf " [%d times]" n) in
        String.concat "\n" lines
    in
 Printf.eprintf "%s\nAnomaly: %s %s\n%!" trace (pp_loc_opt loc) s;
  exit 2
let default_type_error ?loc s = default_error ?loc s

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

let option_map f = function
  | Some x -> Some (f x)
  | None -> None
let option_smart_map f = function
  | Some x as orig -> let x' = f x in if x' == x then orig else Some x'
  | None -> None
let option_mapacc f acc = function
  | Some x -> let acc, y = f acc x in acc, Some y
  | None -> acc, None
let option_iter f = function None -> () | Some x -> f x
let option_default d = function None -> d | Some x -> x

module Pair = struct

  let pp poly_a poly_b fmt x =
    let (x0, x1) = x in
    Format.pp_open_box fmt 1;
    Format.pp_print_string fmt "(";
    Format.pp_open_box fmt 0;
    poly_a fmt x0;
    Format.pp_close_box fmt ();
    Format.pp_print_string fmt ",";
    Format.pp_print_space fmt ();
    Format.pp_open_box fmt 0;
    poly_b fmt x1;
    Format.pp_close_box fmt ();
    Format.pp_print_string fmt ")";
    Format.pp_close_box fmt ()
  let show poly_a poly_b x =
    Format.asprintf "@[%a@]" (pp poly_a poly_b) x
end
let pp_option f fmt = function None -> () | Some x -> f fmt x
let pp_int = Int.pp
let pp_string = String.pp
let pp_pair = Pair.pp
let show_pair = Pair.show

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
   type t = int
   let pp fmt x = Format.pp_print_int fmt x
   let show x = Format.asprintf "@[%a@]" pp x
let _ = show
[@@@end]
   let compare x y = x - y
   let equal x y = x == y
   let hash x = x
 end

 let counter = ref 2
 let make () = incr counter; !counter

 module Htbl = Hashtbl.Make(Self)

 include Self
end

type 'a spaghetti_printer =
  (Format.formatter -> 'a -> unit) ref
let mk_spaghetti_printer () =
  ref (fun fmt _ -> Fmt.fprintf fmt "please extend this printer")
let set_spaghetti_printer r f = r := f

let pp_spaghetti r fmt x = !r fmt x
let show_spaghetti r x =
  let b = Buffer.create 20 in
  let fmt = Format.formatter_of_buffer b in
  Format.fprintf fmt "%a%!" !r x;
  Buffer.contents b

let pp_spaghetti_any r ~id fmt x = !r fmt (id,Obj.repr x)

module CData = struct
  type t = {
    t : Obj.t;
    ty : int;
  }
  type tt = t

  type 'a data_declaration = {
    data_name : string;
    data_pp : Format.formatter -> 'a -> unit;
    data_compare : 'a -> 'a -> int;
    data_hash : 'a -> int;
    data_hconsed : bool;
  }

  type 'a cdata = { cin : 'a -> t; isc : t -> bool; cout: t -> 'a; name : string }
  
  type cdata_declaration = {
    cdata_name : string;
    cdata_pp : Format.formatter -> t -> unit;
    cdata_compare : t -> t -> int;
    cdata_hash : t -> int;
    cdata_canon : t -> t;
  }

let m : cdata_declaration IntMap.t ref = ref IntMap.empty

let cget x = Obj.obj x.t
let pp f x = (IntMap.find x.ty !m).cdata_pp f x
let equal x y = x.ty = y.ty && (IntMap.find x.ty !m).cdata_compare x y == 0
let compare x y =
  if x.ty = y.ty then (IntMap.find x.ty !m).cdata_compare x y
  else type_error "cdata of different type compared"
let hash x = (IntMap.find x.ty !m).cdata_hash x
let name x = (IntMap.find x.ty !m).cdata_name
let hcons x = (IntMap.find x.ty !m).cdata_canon x
let ty2 { isc; _ } ({ ty = t1; _ } as x) { ty = t2; _ } = isc x && t1 = t2
let show x =
  let b = Buffer.create 22 in
  Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" pp x;
  Buffer.contents b

let fresh_tid =
  let tid = ref 0 in
  fun () -> incr tid; !tid

let declare { data_compare; data_pp; data_hash; data_name; data_hconsed } =
  let tid = fresh_tid () in
  let cdata_compare x y = data_compare (cget x) (cget y) in
  let cdata_hash x = data_hash (cget x) in
  let cdata_canon =
    if data_hconsed then
      let module CD : Hashtbl.HashedType with type t = tt = struct
        type t = tt
        let hash = cdata_hash
        let equal x y = cdata_compare x y == 0
      end in
      let module HS : Weak.S with type data = tt = Weak.Make(CD) in
      let h = HS.create 17 in
      (fun x -> try HS.find h x
                with Not_found -> HS.add h x; x)
    else (fun x -> x) in
  let cdata_compare_hconsed =
    if data_hconsed then (fun x y -> if x == y then 0 else cdata_compare x y)
    else cdata_compare in
  m := IntMap.add tid { cdata_name = data_name;
                   cdata_pp = (fun f x -> data_pp f (cget x));
                   cdata_compare = cdata_compare_hconsed;
                   cdata_hash;
                   cdata_canon;
       } !m;
  {
    cin = (fun v -> cdata_canon { t = Obj.repr v; ty = tid });
    isc = (fun c -> c.ty = tid);
    cout = (fun c -> assert(c.ty = tid); cget c);
    name = data_name;
  }

  let morph1 { cin; cout; _ } f x = cin (f (cout x))
  let morph2 { cin; cout; _ } f x y = cin (f (cout x) (cout y))
  
  let map { cout; _ } { cin; _ } f x = cin (f (cout x))
end

let make_absolute cwd filename =
  if not (Filename.is_relative filename) then filename
  else Filename.concat cwd filename

let rec readsymlinks f =
  try
    let link = Unix.readlink f in
    if not(Filename.is_relative link) then readsymlinks link
    else readsymlinks Filename.(concat (dirname f) link)
  with Unix.Unix_error _ | Failure _ -> f
  
exception File_not_found of string

let std_resolver ?(cwd=Sys.getcwd()) ~paths () =
  let dirs = List.map (fun f -> make_absolute cwd (readsymlinks f)) paths in
fun ?(cwd=Sys.getcwd()) ~unit:(origfilename as filename) () ->
  let rec iter_tjpath dirnames =
    let filename,dirnames,relative =
     if not (Filename.is_relative filename) then filename,[],false
     else
      match dirnames with
         [] -> raise (File_not_found filename)
       | dirname::dirnames->Filename.concat dirname filename,dirnames,true in
    let prefixname = Filename.remove_extension filename in
     let change_suffix filename =
      if Filename.check_suffix filename ".elpi" then
       (* Backward compatibility with Teyjus *) 
       prefixname ^ ".mod"
      else if Filename.check_suffix filename ".mod" then
       (* Forward compatibility with Teyjus *) 
       prefixname ^ ".elpi"
      else filename in
     if Sys.file_exists filename then filename
     else
      let changed_filename = change_suffix filename in
      if Sys.file_exists changed_filename then changed_filename
      else if relative then iter_tjpath dirnames
      else raise (File_not_found origfilename)
  in
  try iter_tjpath (cwd :: dirs)
  with File_not_found f ->
    raise (Failure ("File "^f^" not found in: " ^ String.concat ", " dirs))


(* Used by pretty printers, to be later instantiated in module Constants *)
let pp_const = mk_spaghetti_printer ()
type constant = int (* De Bruijn levels *) [@@ deriving ord]
let pp_constant = pp_spaghetti pp_const
let show_constant = show_spaghetti pp_const
let equal_constant x y = x == y

module Constants : sig
  type t = constant
  module Map : Map.S with type key = constant
  module Set : Set.S with type elt = constant
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val compare : t -> t -> int
end = struct

module Self = struct
  type t = constant
  let compare x y = x - y
  let pp = pp_constant
  let show = show_constant
end
module Map = Map.Make(Self)
module Set = Set.Make(Self)
include Self
end
