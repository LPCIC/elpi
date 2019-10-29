(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "namespace00"
  ~source_elpi:"namespaces00.elpi"
  ~description:"namespacing of predicates and constants"
  ()
let () = declare "namespace01"
  ~source_elpi:"namespaces01.elpi"
  ~description:"namespacing of predicates and constants"
  ()
let () = declare "namespace02"
  ~source_elpi:"namespaces02.elpi"
  ~description:"namespacing of predicates and constants"
  ()
let () = declare "namespace03"
  ~source_elpi:"namespaces03.elpi"
  ~description:"namespacing of predicates and constants"
  ()

let () = declare "shorten"
  ~source_elpi:"shorten.elpi"
  ~description:"shortening names of a namespace"
  ()
let () = declare "shorten-EOF"
  ~source_elpi:"shorten2.elpi"
  ~description:"shortening names ends with the file"
  ()
let () = declare "shorten_trie"
  ~source_elpi:"shorten_trie.elpi"
  ~description:"shortening a trie of names"
  ()
let () = declare "shorten_builtin"
  ~source_elpi:"shorten_builtin.elpi"
  ~description:"shortening a builtin"
  ()

let () = declare "named_clauses00"
  ~source_elpi:"named_clauses00.elpi"
  ~description:"clause grafting using names"
  ~expectation:Test.Failure
  ()
let () = declare "named_clauses01"
  ~source_elpi:"named_clauses01.elpi"
  ~description:"clause grafting using names"
  ~expectation:Test.Failure
  ()

let () = declare "named_clauses02"
  ~source_elpi:"named_clauses02.elpi"
  ~description:"clause grafting using names"
  ()

let () = declare "discard"
  ~source_elpi:"discard.elpi"
  ~description:"_"
  ()

let () = declare "chr"
  ~source_elpi:"chr.elpi"
  ~description:"constraints handling rules"
  ()

let () = declare "chr_leq"
  ~source_elpi:"chrLEQ.elpi"
  ~description:"chr transitive closure"
  ()

let () = declare "chr_nokey"
  ~source_elpi:"chr_nokey.elpi"
  ~description:"constraints keyed on _"
  ()

let () = declare "chr_gcd"
  ~source_elpi:"chrGCD.elpi"
  ~description:"greatest common divisor in CHR"
  ()

let () = declare "chr_nokey2"
  ~source_elpi:"chr_nokey2.elpi"
  ~description:"constraints keyed on _"
  ()

let () = declare "chr_sem"
  ~source_elpi:"chr_sem.elpi"
  ~description:"refined operational semantics"
  ()

let () = declare "chr_ut"
  ~source_elpi:"llamchr.elpi"
  ~description:"type checker with UT via CHR"
  ()

let () = declare "chr_even_odd"
  ~source_elpi:"even-odd.elpi"
  ~description:"CHR example at MLWS"
  ()
let () = declare "w"
  ~source_elpi:"w.elpi"
  ~description:"ELPI example at MLWS"
  ()
let () = declare "uvar_keyword"
  ~source_elpi:"uvar_chr.elpi"
  ~description:"uvar kwd status at the meta level"
  ()
let () = declare "polymorphic_variants"
  ~source_elpi:"polymorphic_variants.elpi"
  ~description:"typechecker for polymorphic variants"
  ()


let () = declare "impl_order"
  ~source_elpi:"ctx_loading.elpi"
  ~description:"implication and pair/list"
  ()
let () = declare "list_as_conj"
  ~source_elpi:"list_as_conj.elpi"
  ~description:"list is an nary conjunction"
  ()

let () = declare "spilling_lam"
  ~source_elpi:"spill_lam.elpi"
  ~description:"spilling inside anonymous clause"
  ()

let () = declare "spilling_impl"
  ~source_elpi:"spill_impl.elpi"
  ~description:"spilling implication"
  ()

let () = declare "spilling_and"
  ~source_elpi:"spill_and.elpi"
  ~description:"spilling anonymous compound goal"
  ()

let () = declare "block"
  ~source_elpi:"block.elpi"
  ~description:"blocks are closed"
  ~expectation:Test.Failure
  ()

let () = declare "elpi_only_llam"
  ~source_elpi:"elpi_only_llam.elpi"
  ~description:"full HO unif gives error"
  ~expectation:Test.Failure
  ()

let () = declare "hollight"
  ~source_elpi:"hollight.elpi"
  ~description:"hollinght implementation"
  ~expectation:Test.Failure (* needs advanced modes *)
  ()

let () = declare "asclause"
  ~source_elpi:"asclause.elpi"
  ~description:"parsing of the .. as X clause"
  ~expectation:Test.Success
  ()

let () = declare "elpi-checker"
  ~source_elpi:"elpi-checker.elpi"
  ~description:"type checking the type checker"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "elpi2html"
  ~source_elpi:"elpi2html.elpi"
  ~description:"type checking elpi2html"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "same_term"
  ~source_elpi:"same_term.elpi"
  ~description:"the == operator"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "list_comma"
  ~source_elpi:"list_comma.elpi"
  ~description:"lists with spurious , in there"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "heap_discard"
  ~source_elpi:"heap_discard.elpi"
  ~description:"heapification of _"
  ~typecheck:true
  ~expectation:Test.Success
  ()
