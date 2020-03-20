let () =
  let inf, outf = ref "", ref "" in
  let rec args b i =
    if i = Array.length Sys.argv then exit 1;
    let arg = Sys.argv.(i) in
    if arg.[0] == '-' then args b (i+1)
    else
      if b then outf := arg
      else (inf := arg; args true (i+1)) in
  args false 1;
  let i = open_in !inf in
  let o = open_out !outf in
  try
    while true do
      output_char o (input_char i)
    done
  with _ -> exit 0