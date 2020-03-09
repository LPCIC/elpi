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
  ~typecheck:false
  ~trace:(On["json";"stdout";"-trace-at";"1";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutput (Str.regexp "user:CHR:rule-fired"))
  ()
let () = declare "w"
  ~source_elpi:"w.elpi"
  ~description:"ELPI example at MLWS"
  ()
let () = declare "w_legacy"
  ~source_elpi:"w_legacy.elpi"
  ~legacy_parser:true
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
  ~description:"hollight implementation"
  ~expectation:Test.Failure (* needs advanced modes *)
  ()
let () = declare "hollight_legacy"
  ~source_elpi:"hollight_legacy.elpi"
  ~description:"hollight implementation"
  ~expectation:Test.Failure (* needs advanced modes *)
  ~legacy_parser:true
  ()

let () = declare "asclause"
  ~source_elpi:"asclause.elpi"
  ~description:"parsing of the .. as X clause"
  ~expectation:Test.Success
  ()

let () = declare "elpi-checker"
  ~source_elpi:"elpi-checker-copy.elpi"
  ~description:"type checking the type checker"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "elpi2html"
  ~source_elpi:"elpi2html-copy.elpi"
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

let () = declare "accumulate_twice1"
  ~source_elpi:"accumulate_twice1.elpi"
  ~description:"double accumulate"
  ~typecheck:true
  ~expectation:Test.Failure
  ()
let () = declare "accumulate_twice2"
  ~source_elpi:"accumulate_twice2.elpi"
  ~description:"double accumulate"
  ~typecheck:true
  ~expectation:Test.Failure
  ()

let () = declare "CHR_no_clique"
  ~source_elpi:"chr_not_clique.elpi"
  ~description:"CHR rule on a non constraint"
  ~typecheck:true
  ~expectation:Test.Failure
  ()

let () = declare "quote_syntax"
  ~source_elpi:"quote_syntax.elpi"
  ~description:"quote_syntax API"
  ~typecheck:true
  ~expectation:(Test.SuccessOutput (Str.regexp "const main"))
  ()

let () = declare "var"
  ~source_elpi:"var.elpi"
  ~description:"var API"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "hyp_uvar"
  ~source_elpi:"hyp_uvar.elpi"
  ~description:"uvar at the left of implication"
  ~typecheck:true
  ~expectation:Test.Success
  ()

let () = declare "trailing_comment"
  ~source_elpi:"end_comment.elpi"
  ~description:"trailing comment"
  ~expectation:Test.Success
  ()

let () = declare "variadic_declare_constraints"
  ~source_elpi:"variadic_declare_constraints.elpi"
  ~description:"declare_constraint takes keys of different types"
  ~expectation:Test.Success
  ()

let () = declare "notation_error"
  ~source_elpi:"notation_error.elpi"
  ~description:"infix declaration error"
  ~expectation:Test.(FailureOutput (Str.regexp "not supported by this parser"))
  ()

let () = declare "printer"
  ~source_elpi:"printer.elpi"
  ~description:"printing infix"
  ~typecheck:false
  ~expectation:Test.(SuccessOutput (Str.regexp_string (
    Str.global_replace (Str.regexp_string "\r") "" {|p X0 :- q X0 , r x
X0 is f X1 mod r X0
X0 is f X1 + r X0 * g X2
X0 is (f X1 + r X0) * g X2
X0 is f X1 ^ r X0 ^ g X2
X0 || X2 && X3 ==> X4
[f X0, g X1, (a , b), a + b]
|})))
  ()
