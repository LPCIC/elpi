open Elpi_runtime.Runtime

let rec sorted = function
  | [] -> true
  | [ _ ] -> true
  | x :: (y :: _ as l) ->
      let r = lex_insertion x y < 0 in
      if not r then Format.(eprintf "Not sorted [%a] [%a]\n" (pp_print_list pp_print_int) x (pp_print_list pp_print_int) y);
      r && sorted l

let () =
  assert (lex_insertion [] [] = 0);

  (* test 1 *)
  assert( sorted [ [-1] ; [0]   ; [1;-1]; [1;-2];         [1]   ; [1;2] ; [1;1] ; [2]   ; ]);
  assert( sorted [ [-1] ; [0]   ; [1;-1]; [1;-2]; [1;-3]; [1]   ; [1;2] ; [1;1] ; [2]   ; ]);

  assert( sorted [ [1;-1]; [2;-2]; ]);
  assert( sorted [ [-1]; [0]; [1] ]);
  assert( sorted [ [-2]; [-1]; [0] ]);
  assert( sorted [ [241]; [242;-1]; [243] ]);

  assert(lex_insertion[243] [242;-1] > 0);
  assert(lex_insertion [242;-1] [241] > 0);
  assert(lex_insertion [241] [242;-1] < 0);

  assert(lex_insertion [242;0;9] [242;-1;9] > 0);
  assert(lex_insertion [242;0;9] [242;-1;8] > 0);
;; 

