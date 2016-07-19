type identifier = string

(* Util.ml *)

let is_digit c = (c >= '0' && c <= '9')

(* Nameops.ml *)

let has_subscript id =
  is_digit (id.[String.length id - 1])

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

let cut_ident skip_quote s =
  let slen = String.length s in
  (* [n'] is the position of the first non nullary digit *)
  let rec numpart n n' =
    if n = 0 then
      (* ident made of _ and digits only [and ' if skip_quote]: don't cut it *)
      slen
    else
      let c = Char.code (String.get s (n-1)) in
      if c = code_of_0 && n <> slen then
        numpart (n-1) n'
      else if code_of_0 <= c && c <= code_of_9 then
        numpart (n-1) (n-1)
      else if skip_quote & (c = Char.code '\'' || c = Char.code '_') then
        numpart (n-1) (n-1)
      else
        n'
  in
  numpart slen slen

let forget_subscript id =
  let numstart = cut_ident false id in
  let newid = String.make (numstart+1) '0' in
  String.blit id 0 newid 0 numstart;
  newid

(* Namegen.ml *)

let restart_subscript id =
  if not (has_subscript id) then id else
    (* Ce serait sans doute mieux avec quelque chose inspiré de
     *** make_ident id (Some 0) *** mais ça brise la compatibilité... *)
    forget_subscript id

(* Rem: semantics is a bit different, if an ident starts with toto00 then
  after successive renamings it comes to toto09, then it goes on with toto10 *)
let lift_subscript id =
  let len = String.length id in
  let rec add carrypos =
    let c = id.[carrypos] in
    if is_digit c then
      if c = '9' then begin
        assert (carrypos>0);
        add (carrypos-1)
      end
      else begin
        let newid = String.copy id in
        String.fill newid (carrypos+1) (len-1-carrypos) '0';
        newid.[carrypos] <- Char.chr (Char.code c + 1);
        newid
      end
    else begin
      let newid = id^"0" in
      if carrypos < len-1 then begin
        String.fill newid (carrypos+1) (len-1-carrypos) '0';
        newid.[carrypos+1] <- '1'
      end;
      newid
    end
  in add (len-1)

let next_ident_away_from id bad =
  let rec name_rec id = if bad id then name_rec (lift_subscript id) else id in
  name_rec id

let next_ident_away id avoid =
  if List.mem id avoid then
    next_ident_away_from (restart_subscript id) (fun id -> List.mem id avoid)
  else id

(* ----- *)

type label
type reference

type env
type constant_body
type ('a,'b) prec_declaration

type module_path
type mod_bound_id

module Intmap = Map.Make(struct type t = int let compare = compare end)

module Intset = Set.Make(struct type t = int let compare = compare end)

module Idset = Set.Make(struct type t = identifier let compare = compare end)

module Uriset = Set.Make(struct type t = NUri.uri let compare = NUri.compare end)

module Refmap = Map.Make(struct type t = NReference.reference let compare = NReference.compare end)

module Stringmap = Map.Make(String)

(* Pp_control.ml *)

module Pp_control =
 struct
  let with_output_to _ = assert false
  let get_margin _ = assert false
 end

(* Util.ml *)

let list_map_i f =
  let rec map_i_rec i = function
    | [] -> []
    | x::l -> let v = f i x in v :: map_i_rec (i+1) l
  in
  map_i_rec

let list_map_i_status status f =
  let rec map_i_rec status i = function
    | [] -> status,[]
    | x::l -> let status,v = f status i x in
      let status,res = map_i_rec status (i+1) l in
       status,v :: res
  in
  map_i_rec status

let iterate f =
  let rec iterate_f n x =
    if n <= 0 then x else iterate_f (pred n) (f x)
  in
  iterate_f

let rec list_skipn n l = match n,l with
  | 0, _ -> l
  | _, [] -> failwith "list_skipn"
  | n, _::l -> list_skipn (pred n) l

let list_split_at index l =
  let rec aux i acc = function
      tl when i = index -> (List.rev acc), tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "list_split_at: Invalid argument"
  in aux 0 [] l

let list_chop n l =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "list_chop"
  in
  chop_aux [] (n,l)

let list_firstn n l =
  let rec aux acc = function
    | (0, _l) -> List.rev acc
    | (n, (h::t)) -> aux (h::acc) (pred n, t)
    | _ -> failwith "firstn"
  in
  aux [] (n,l)

let list_fold_left_i f =
  let rec it_list_f i a = function
    | [] -> a
    | b::l -> it_list_f (i+1) (f i a b) l
  in
  it_list_f

let list_iter_i f l = list_fold_left_i (fun i _ x -> f i x) 0 () l

let list_lastn n l =
  let len = List.length l in
  let rec aux m l =
    if m = n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

let array_map2 f v1 v2 =
  if Array.length v1 <> Array.length v2 then invalid_arg "array_map2";
  if Array.length v1 == 0 then
    [| |]
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i)
    done;
    res
  end

let array_for_all f v =
  let rec allrec = function
    | -1 -> true
    | n -> (f v.(n)) && (allrec (n-1))
  in
  allrec ((Array.length v)-1)

let array_fold_right_i f v a =
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f k v.(k) a) k in
  fold a (Array.length v)

let identity x = x

let interval n m =
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l,pred m)
  in
  interval_n ([],m)

let map_status status f l =
 List.fold_right
  (fun x (status,res)->let status,y = f status x in status,y::res) l (status,[])

(* CSC: Inefficiently implemented *)
let array_map_status status f l =
 let status,res = map_status status f (Array.to_list l) in
  status,Array.of_list res

(* CSC: Inefficiently implemented *)
let array_mapi_status status f l =
 let status,res = list_map_i_status status f 0 (Array.to_list l) in
  status,Array.of_list res

(* Pp.ml4 *)

type block_type =
  | Pp_hbox of int
  | Pp_vbox of int
  | Pp_hvbox of int
  | Pp_hovbox of int
  | Pp_tbox

type 'a ppcmd_token =
  | Ppcmd_print of 'a
  | Ppcmd_box of block_type * ('a ppcmd_token Stream.t)
  | Ppcmd_print_break of int * int
  | Ppcmd_set_tab
  | Ppcmd_print_tbreak of int * int
  | Ppcmd_white_space of int
  | Ppcmd_force_newline
  | Ppcmd_print_if_broken
  | Ppcmd_open_box of block_type
  | Ppcmd_close_box
  | Ppcmd_close_tbox
  | Ppcmd_comment of int

type ppcmd = (int*string) ppcmd_token

type std_ppcmds = ppcmd Stream.t

type 'a ppdir_token =
  | Ppdir_ppcmds of 'a ppcmd_token Stream.t
  | Ppdir_print_newline
  | Ppdir_print_flush

let utf8_length s =
  let len = String.length s
  and cnt = ref 0
  and nc = ref 0
  and p = ref 0 in
  while !p < len do
    begin
      match s.[!p] with
      | '\000'..'\127' -> nc := 0 (* ascii char *)
      | '\128'..'\191' -> nc := 0 (* cannot start with a continuation byte *)
      | '\192'..'\223' -> nc := 1 (* expect 1 continuation byte *)
      | '\224'..'\239' -> nc := 2 (* expect 2 continuation bytes *)
      | '\240'..'\247' -> nc := 3 (* expect 3 continuation bytes *)
      | '\248'..'\251' -> nc := 4 (* expect 4 continuation bytes *)
      | '\252'..'\253' -> nc := 5 (* expect 5 continuation bytes *)
      | '\254'..'\255' -> nc := 0 (* invalid byte *)
    end ;
    incr p ;
    while !p < len && !nc > 0 do
      match s.[!p] with
      | '\128'..'\191' (* next continuation byte *) -> incr p ; decr nc
      | _ (* not a continuation byte *) -> nc := 0
    done ;
    incr cnt
  done ;
  !cnt

let (++) = Stream.iapp
let str s = [< 'Ppcmd_print (utf8_length s,s) >]
let spc () = [< 'Ppcmd_print_break (1,0) >]
let mt () = [< >]
let v n s = [< 'Ppcmd_box(Pp_vbox n,s) >]
let hv n s = [< 'Ppcmd_box(Pp_hvbox n,s) >]
let hov n s = [< 'Ppcmd_box(Pp_hovbox n,s) >]
let int n = str (string_of_int n)
let stras (i,s) = [< 'Ppcmd_print (i,s) >]
let fnl () = [< 'Ppcmd_force_newline >]

let com_eol = ref false

let com_brk _ft = com_eol := false
let com_if ft f =
  if !com_eol then (com_eol := false; Format.pp_force_newline ft ())
  else Lazy.force f

let comments = ref []

let rec split_com comacc acc pos = function
    [] -> comments := List.rev acc; comacc
  | ((b,e),c as com)::coms ->
      (* Take all comments that terminates before pos, or begin exactly
         at pos (used to print comments attached after an expression) *)
      if e<=pos || pos=b then split_com (c::comacc) acc pos coms
      else  split_com comacc (com::acc) pos coms

let rec pr_com ft s =
  let (s1,os) =
    try
      let n = String.index s '\n' in
      String.sub s 0 n, Some (String.sub s (n+1) (String.length s - n - 1))
    with Not_found -> s,None in
  com_if ft (Lazy.lazy_from_val());
(*  let s1 =
    if String.length s1 <> 0 && s1.[0] = ' ' then
      (Format.pp_print_space ft (); String.sub s1 1 (String.length s1 - 1))
    else s1 in*)
  Format.pp_print_as ft (utf8_length s1) s1;
  match os with
      Some s2 ->
        if String.length s2 = 0 then (com_eol := true)
        else
          (Format.pp_force_newline ft (); pr_com ft s2)
    | None -> ()

let pp_dirs ft =
  let pp_open_box = function
    | Pp_hbox _n   -> Format.pp_open_hbox ft ()
    | Pp_vbox n   -> Format.pp_open_vbox ft n
    | Pp_hvbox n  -> Format.pp_open_hvbox ft n
    | Pp_hovbox n -> Format.pp_open_hovbox ft n
    | Pp_tbox     -> Format.pp_open_tbox ft ()
  in
  let rec pp_cmd = function
    | Ppcmd_print(n,s)        ->
        com_if ft (Lazy.lazy_from_val()); Format.pp_print_as ft n s
    | Ppcmd_box(bty,ss)       -> (* Prevent evaluation of the stream! *)
        com_if ft (Lazy.lazy_from_val());
        pp_open_box bty ;
        if not (Format.over_max_boxes ()) then Stream.iter pp_cmd ss;
        Format.pp_close_box ft ()
    | Ppcmd_open_box bty      -> com_if ft (Lazy.lazy_from_val()); pp_open_box bty
    | Ppcmd_close_box         -> Format.pp_close_box ft ()
    | Ppcmd_close_tbox        -> Format.pp_close_tbox ft ()
    | Ppcmd_white_space n     ->
        com_if ft (Lazy.lazy_from_fun (fun()->Format.pp_print_break ft n 0))
    | Ppcmd_print_break(m,n)  ->
        com_if ft (Lazy.lazy_from_fun(fun()->Format.pp_print_break ft m n))
    | Ppcmd_set_tab           -> Format.pp_set_tab ft ()
    | Ppcmd_print_tbreak(m,n) ->
        com_if ft (Lazy.lazy_from_fun(fun()->Format.pp_print_tbreak ft m n))
    | Ppcmd_force_newline     ->
        com_brk ft; Format.pp_force_newline ft ()
    | Ppcmd_print_if_broken   ->
        com_if ft (Lazy.lazy_from_fun(fun()->Format.pp_print_if_newline ft ()))
    | Ppcmd_comment i         ->
        let coms = split_com [] [] i !comments in
(*        Format.pp_open_hvbox ft 0;*)
        List.iter (pr_com ft) coms(*;
        Format.pp_close_box ft ()*)
  in
  let pp_dir = function
    | Ppdir_ppcmds cmdstream -> Stream.iter pp_cmd cmdstream
    | Ppdir_print_newline    ->
        com_brk ft; Format.pp_print_newline ft ()
    | Ppdir_print_flush      -> Format.pp_print_flush ft ()
  in
  fun dirstream ->
    try
      Stream.iter pp_dir dirstream; com_brk ft
    with
      | e -> Format.pp_print_flush ft () ; raise e

let pp_with ft strm =
  pp_dirs ft [< 'Ppdir_ppcmds strm >]

(* Util.ml *)

let rec prlist_with_sep sep elem l = match l with
  | []   -> mt ()
  | [h]  -> elem h
  | h::t ->
      let e = elem h and s = sep() and r = prlist_with_sep sep elem t in
      e ++ s ++ r

let rec prlist_with_sep_status status sep elem l = match l with
  | []   -> status,mt ()
  | [h]  -> elem status h
  | h::t ->
      let status,e = elem status h in
      let s = sep() in
      let status,r = prlist_with_sep_status status sep elem t in
      status, e ++ s ++ r

let rec prlist elem l = match l with
  | []   -> mt ()
  | h::t -> Stream.lapp (fun () -> elem h) (prlist elem t)

let rec prlist_strict elem l = match l with
  | []   -> mt ()
  | h::t ->
      let e = elem h in let r = prlist_strict elem t in e++r

let prvecti_with_sep sep elem v =
  let rec pr i =
    if i = 0 then
      elem 0 v.(0)
    else
      let r = pr (i-1) and s = sep () and e = elem i v.(i) in
      r ++ s ++ e
  in
  let n = Array.length v in
  if n = 0 then mt () else pr (n - 1)

let prvecti_with_sep_status status sep elem v =
  let rec pr status i =
    if i = 0 then
     elem status 0 v.(0)
    else
      let status,r = pr status (i-1) in
      let s = sep () in
      let status,e = elem status i v.(i) in
      status, r ++ s ++ e
  in
  let n = Array.length v in
  if n = 0 then status,mt () else pr status (n - 1)

let prvecti elem v = prvecti_with_sep mt elem v

let prvecti_status status elem v = prvecti_with_sep_status status mt elem v

let prvect_with_sep sep elem v = prvecti_with_sep sep (fun _ -> elem) v

let prvect_with_sep_status status sep elem v =
 prvecti_with_sep_status status sep (fun status _ -> elem status) v

let prvect elem v = prvect_with_sep mt elem v

(* Nameops.ml *)

let pr_id id = str id

(* ---- *)
