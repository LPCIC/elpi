
let debug = ref false
let first_step = ref 0
let last_step = ref max_int
let cur_step = ref 0
let level = ref 0

let condition () = !debug && !cur_step >= !first_step && !cur_step <= !last_step

let init ?(first=0) ?(last=max_int) b =
  cur_step := 0; first_step := first; last_step := last; debug := b

let enter k msg =
  incr level;
  incr cur_step;
  if condition () then
    Printf.eprintf "%s%s %d {{{ %s\n"
      (String.make !level ' ') k !cur_step (Lazy.force msg)

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

let exit ?(e=OK) () =
  decr level; 
  if condition () then
    Printf.eprintf "%s}}} %s\n" (String.make !level ' ') (pr_exc e)


