(* Conversions between byte offsets in a text (what Elpi locations use) and
   LSP positions: 0-based lines and columns counted in UTF-16 code units. *)

type t = {
  text : string;
  line_starts : int array; (* byte offset of the beginning of each line *)
}

let make text =
  let starts = ref [0] in
  String.iteri (fun i c -> if c = '\n' then starts := (i + 1) :: !starts) text;
  { text; line_starts = Array.of_list (List.rev !starts) }

let length t = String.length t.text

(* the line containing byte [off], by binary search *)
let line_of_offset t off =
  let rec search lo hi = (* line_starts.(lo) <= off < line_starts.(hi) *)
    if hi - lo <= 1 then lo
    else
      let mid = (lo + hi) / 2 in
      if t.line_starts.(mid) <= off then search mid hi else search lo mid in
  search 0 (Array.length t.line_starts)

(* number of UTF-16 code units of the UTF-8 character starting with byte c,
   0 for a continuation byte *)
let utf16_units c =
  let c = Char.code c in
  if c land 0xC0 = 0x80 then 0
  else if c >= 0xF0 then 2
  else 1

let position_of_offset t off : Lsp.Types.Position.t =
  let off = max 0 (min off (length t)) in
  let line = line_of_offset t off in
  let character = ref 0 in
  for i = t.line_starts.(line) to off - 1 do
    character := !character + utf16_units t.text.[i]
  done;
  { line; character = !character }

let offset_of_position t ({ line; character } : Lsp.Types.Position.t) =
  if line < 0 then 0
  else if line >= Array.length t.line_starts then length t
  else
    let stop =
      if line + 1 < Array.length t.line_starts then t.line_starts.(line + 1) - 1
      else length t in
    let rec go i units =
      if i >= stop || units >= character then i
      else
        (* skip the whole character *)
        let j = ref (i + 1) in
        while !j < stop && utf16_units t.text.[!j] = 0 do incr j done;
        go !j (units + utf16_units t.text.[i]) in
    go t.line_starts.(line) 0

let range t start stop : Lsp.Types.Range.t =
  { start = position_of_offset t start; end_ = position_of_offset t (max start stop) }

(* end of the "word" starting at [off]: used to give a width to errors that
   only have a position; at least one character, at most the end of line *)
let word_end t off =
  let n = length t in
  let is_blank c = c = ' ' || c = '\t' || c = '\n' || c = '\r' in
  if off >= n then n
  else if t.text.[off] = '\n' || t.text.[off] = '\r' then off
  else if is_blank t.text.[off] then off + 1
  else
    let rec go i = if i < n && not (is_blank t.text.[i]) then go (i + 1) else i in
    go off
