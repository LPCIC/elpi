let arity = ref 2
let sum = ref 0.0

let rec loop n =
   if n <= 0 then begin
      print_endline (string_of_float !sum);
      sum := 0.0; loop !arity
   end else begin
      sum := !sum +. read_float ();
      loop (pred n)
   end

let set_arity n =
   if n > 0 then arity := n

let main =
   Arg.parse ["-a", Arg.Int set_arity, ""] ignore "";
   try loop !arity with End_of_file -> ()
   
