let max_profilers = 20;;
let profiler_no = ref 0;;
let profiler_label2int = Hashtbl.create 3;;
let name = ref "";;

let banner _ pname = 
  name := pname; 
 "(Array.make "^string_of_int max_profilers^" (0,0.)), "^
 "(Array.make "^string_of_int max_profilers^" (0.))"
;;

let ensure_label_in_table label =
  if not (Hashtbl.mem profiler_label2int label) then
    begin
      if !profiler_no > max_profilers then
        raise (Invalid_argument "Too many profilers.");
      Hashtbl.add profiler_label2int label !profiler_no;
      incr profiler_no;
    end
;;
  

let start label =
  ensure_label_in_table label;
  let id = Hashtbl.find profiler_label2int label in
  " ((snd "^ !name^").("^string_of_int id^") <- Unix.gettimeofday()) "
;;
      
let stop label extra =
  ensure_label_in_table label;
  let id = Hashtbl.find profiler_label2int label in
  "(let __res = " ^ extra ^ "  in ( "^
  "let interval = Unix.gettimeofday () -. "^
    "(snd "^ !name^").("^string_of_int id^") in "^
  "let oldcount,oldval = (fst "^ !name^").("^string_of_int id^") in "^
  "(fst "^ !name^").("^string_of_int id^") <- "^
    "(oldcount+1,interval +. oldval)); __res )"
;;

let profile_start_stop _ label = 
  let label,extra =
    match Str.bounded_split (Str.regexp "\n") label 2 with
    | [label;extra] -> label,extra
    | _ -> 
        raise (Invalid_argument ("Profiler 'stop' with a bad label:" ^ label))
  in
  let start = start label in
  let stop = stop label extra in
  "let _ = " ^ start ^ " in " ^ stop
;; 

let profile_show _ prefix =
  (Hashtbl.fold 
    (fun k v acc -> 
      acc ^ 
      "let t = (fst "^ !name^").("^string_of_int v^") in "^
      "let acc = acc ^ Printf.sprintf \"%-15s %25s: %8d %8.4f\\n\" \"" ^ 
      prefix ^ "\" \"" ^  k ^
      "\" (fst t) (snd t) in ")
    profiler_label2int "let acc = \"\" in ") ^ " acc "
;;

let profile_start _ label = start label ;;
let profile_stop _ label = 
  let label,extra =
    match Str.bounded_split (Str.regexp "\n") label 2 with
    | [label;extra] -> label,extra
    | [label] -> label,"()"
    | _ -> 
        raise (Invalid_argument ("Profiler 'stop' with a bad label:" ^ label))
  in
  stop label extra
;;

(*
Quotation.add "profiler" (Quotation.ExStr banner);;
Quotation.add "profile" (Quotation.ExStr profile_start_stop);;
Quotation.add "start" (Quotation.ExStr profile_start);;
Quotation.add "stop" (Quotation.ExStr profile_stop);;
Quotation.add "show" (Quotation.ExStr profile_show);;
*)

