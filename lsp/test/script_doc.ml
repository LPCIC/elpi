open Test_lsp_lib

(* documentation and previews: the comment block on the line before a
   declaration is shown on hover (not one separated by a blank line); a
   definition is previewed with the rules that follow its declaration (only
   blank space in between), up to 8 lines; a comment after code on its line
   is not documentation *)
let () = register ~name:"doc" "doc.elpi" (fun file ->
  open_file file;
  hover file "twice 21" 0;
  definition file "twice 21" 0;
  hover file "undocumented _" 0;
  definition file "undocumented _" 0;
  hover file "main :-" 0;
  definition file "main :-" 0;
  (* comments after code on their line are not documentation *)
  hover file "qa, ph" 0;
  hover file "ph, pb" 0;
  hover file "pb 1" 0)
