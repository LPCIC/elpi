(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

let debug = ref false
let where_loc = ref ("",0,max_int)
module M = Map.Make(String)
let cur_step = ref M.empty
let level = ref 0
let filter = ref []
let hot = ref false

let get_cur_step k = try M.find k !cur_step with Not_found -> 0

let condition k =
  !debug &&
    let loc, first_step, last_step = !where_loc in
    ((!hot && k <> loc) ||
       (k = loc &&
       let cur_step = get_cur_step k in
       hot := cur_step >= first_step && cur_step <= last_step;
       !hot))
    && not(List.exists (fun p -> Str.string_match p k 0) !filter)

let init ?(where="",0,max_int) ?(filter_out=[]) b =
  cur_step := M.empty;
  debug := b;
  filter := List.map Str.regexp filter_out;
  where_loc := where

let incr_cur_step k =
  let n = get_cur_step k in
  cur_step := M.add k (n+1) !cur_step

let enter k msg =
  incr level;
  incr_cur_step k;
  if condition k then begin
    Format.pp_open_hvbox Format.err_formatter !level;
    Format.eprintf "%s%s %d {{{@[<hv1> %a@]\n%!"
      (String.make !level ' ') k (get_cur_step k) (fun fmt () -> msg fmt) ();
  end

let print name f x = 
  if condition name then
    Format.eprintf "%s %s =@[<hv1> %a@]\n%!" (String.make !level ' ') name f x

let printers = ref []

exception Unknown
exception OK

let pr_exc = function
  | OK -> "ok"
  | e ->
     let rec aux = function
       | [] -> "error: " ^Printexc.to_string e
       | f :: fs ->
             try f e
             with Unknown -> aux fs in
     aux !printers
let pr_exn f = printers := f :: !printers

let exit k ?(e=OK) time =
  if condition k then
    Format.eprintf "%s}}} %s  (%.3fs)\n%!"
      (String.make !level ' ') (pr_exc e) time;
  decr level

