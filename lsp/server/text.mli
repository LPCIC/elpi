(* Conversions between byte offsets in a text (what Elpi locations use) and
   LSP positions: 0-based lines and columns counted in UTF-16 code units. *)

(** a text, with the offsets of its lines *)
type t = private {
  text : string;
  line_starts : int array; (** byte offset of the beginning of each line *)
}

val make : string -> t

(** the position of a byte offset (clamped to the text) *)
val position_of_offset : t -> int -> Lsp.Types.Position.t

(** the byte offset of a position: a line or a column out of the text is
    clamped to it (the end of the line, the end of the text) *)
val offset_of_position : t -> Lsp.Types.Position.t -> int

(** [range t start stop] is the range of the bytes [start] to [stop] *)
val range : t -> int -> int -> Lsp.Types.Range.t

(** the end of the "word" starting at an offset: used to give a width to
    errors that only have a position; at least one character, at most the end
    of the line *)
val word_end : t -> int -> int
