(* A stub module for ANSITerminal, to be expanded as necessary *)

module ANSITerminal = struct
  let green = ()
  let red = ()
  let blue = ()
  let yellow = ()
  let printf _ = Printf.printf

  type loc = Eol

  let move_bol () = Printf.printf "\n%!"
  let erase _ = ()
end
