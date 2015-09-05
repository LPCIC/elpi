open Pcre

let sig_stuff = regexp "^(sig|accum_sig)"
let module_header = regexp "^module "
let imp_accum = regexp "^(accumulate|import)\s+(\w+)\."
let imp_accum_repl = subst "$1 tz_$2."

let print_terzo_stuff oc =
  output_string oc "import terzo_stuff.\n"

let create_terzo name =
  let md = name ^ ".mod"
  and sg = name ^ ".sig"
  and sig_lines = ref []
  and mod_lines = ref [] in
  let dest_md = "tz_" ^ md in

  let in_file = open_in sg in
  foreach_line ~ic:in_file (fun line ->
    if pmatch ~rex:sig_stuff line then ()
    else sig_lines := (line ^ "\n") :: !sig_lines);
  close_in in_file;
  sig_lines := List.rev !sig_lines;

  let sig_ofs = ref 0
  and pos = ref 0 in

  let in_file = open_in md in
  foreach_line ~ic:in_file (fun line ->
    if pmatch ~rex:module_header line then ()
    else begin
      if pmatch ~rex:imp_accum line then begin
        let res = replace ~rex:imp_accum ~itempl:imp_accum_repl line in
        mod_lines := (res ^ "\n") :: !mod_lines;
        sig_ofs := !pos end
      else mod_lines := (line ^ "\n") :: !mod_lines;
      incr pos end
  );
  close_in in_file;
  mod_lines := List.rev !mod_lines;

  let out_file = open_out dest_md in
  output_string out_file ("module tz_" ^ name ^ ".");

  for i = 0 to !sig_ofs do
    output_string out_file (List.hd !mod_lines);
    mod_lines := List.tl !mod_lines
  done;

  print_terzo_stuff out_file;

  List.iter (output_string out_file) !sig_lines;
  List.iter (output_string out_file) !mod_lines;
  close_out out_file

let _ =
  let modules = List.tl (Array.to_list Sys.argv) in
  List.iter create_terzo modules;

  let main_file = "tz_main" in
  let out_file = open_out main_file in
  output_string out_file "#!/bin/sh\nprintf \"\\\n";
  output_string out_file "#load \\\"terzo_stuff.mod\\\".\\n\\\n";
  List.iter (fun m ->
    Printf.fprintf out_file "#load \\\"tz_%s.mod\\\".\\n\\\n" m) modules;
  Printf.fprintf out_file "#query tz_main main \\\"$1\\\". \\n\" | Terzo\n";
  close_out out_file;
  Unix.chmod main_file 0o755
