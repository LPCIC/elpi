open Test_lsp_lib

(* The standard library is a file that the server generates and writes on the
   disk: it is read-only, and the determinacy of its code is not checked *)
let () = register ~name:"library" "good.elpi" (fun file ->
  open_file file;
  section "semantic tokens";
  semantic_tokens file;
  match definition_file file "std.map" 4 with
  | None -> print_endline "no file"
  | Some path ->
      Printf.printf "read-only: %b\n" (is_read_only path);
      open_file path;
      close_file path)
