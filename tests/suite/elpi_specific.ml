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
  ~trace:(On["json";"stdout";"-trace-at";"1";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutput (Str.regexp "user:CHR:rule-fired"))
  ()
let () = declare "w"
  ~source_elpi:"w.elpi"
  ~description:"ELPI example at MLWS"
  ()
(* let () = declare "uvar_keyword"
  ~source_elpi:"uvar_chr.elpi"
  ~description:"uvar kwd status at the meta level"
  () *)
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

let () = declare "spilling_or"
  ~source_elpi:"spill_or.elpi"
  ~description:"spilling prem order"
  ()

let () = declare "spilling_in_list"
  ~source_elpi:"spill_in_list.elpi"
  ~description:"spilling prem order"
  ()

let () = declare "spill_pi"
  ~source_elpi:"spill_pi.elpi"
  ~description:"spilling under pi"
  ()

let () = declare "spill_collision"
  ~source_elpi:"spill_collision.elpi"
  ~description:"spilling under 2 pi named the same"
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
  (* ~expectation:Test.(FailureOutput (Str.regexp "Mode is a no more maintained keyword")) needs advanced modes *)
  ~expectation:Test.Failure
  ()

let () = declare "asclause"
  ~source_elpi:"asclause.elpi"
  ~description:"parsing of the .. as X clause"
  ~expectation:Test.Success
  ()
(* 
let () = declare "elpi2html"
  ~source_elpi:"elpi2html-copy.elpi"
  ~description:"type checking elpi2html"
    ~expectation:Test.Success
  () *)

let () = declare "same_term"
  ~source_elpi:"same_term.elpi"
  ~description:"the == operator"
    ~expectation:Test.Success
  ()

let () = declare "list_comma"
  ~source_elpi:"list_comma.elpi"
  ~description:"lists with spurious , in there"
    ~expectation:Test.Success
  ()

let () = declare "heap_discard"
  ~source_elpi:"heap_discard.elpi"
  ~description:"heapification of _"
    ~expectation:Test.Success
  ()

let () = declare "accumulate_twice1"
  ~source_elpi:"accumulate_twice1.elpi"
  ~description:"double accumulate"
    ~expectation:Test.Failure
  ()
let () = declare "accumulate_twice2"
  ~source_elpi:"accumulate_twice2.elpi"
  ~description:"double accumulate"
    ~expectation:Test.Failure
  ()

let () = declare "CHR_no_clique"
  ~source_elpi:"chr_not_clique.elpi"
  ~description:"CHR rule on a non constraint"
    ~expectation:Test.Failure
  ()

(* needs quote_syntax
let () = declare "quote_syntax"
 ~source_elpi:"quote_syntax.elpi"
  ~description:"quote_syntax API"
    ~expectation:(Test.SuccessOutput (Str.regexp "const main"))
  () *)

let () = declare "var"
  ~source_elpi:"var.elpi"
  ~description:"var API"
    ~expectation:Test.Success
  ()

let () = declare "hyp_uvar"
  ~source_elpi:"hyp_uvar.elpi"
  ~description:"uvar at the left of implication"
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
  ~expectation:Test.(SuccessOutput (Str.regexp_string (
    Str.global_replace (Str.regexp_string "\r") "" {|p X0 :- q X0 , r x
X0 is f X1 mod r X0
X0 is f X1 + r X0 * g X2
X0 is (f X1 + r X0) * g X2
X0 is f X1 ^ r X0 ^ g X2
X0 || X2 && X3 ===> X4
[f X0, g X1, (a , b), a + b]
|})))
  ()

let () = declare "linear"
  ~source_elpi:"linear.elpi"
  ~description:"linear variable check"
    ~expectation:Test.(SuccessOutput (Str.regexp_string "Foo_Bar is linear"))
  ()


let () = declare "IO_COLON"
  ~source_elpi:"io_colon.elpi"
  ~description:"IO_COLON token"
    ()

let () = declare "graft_replace_ok"
  ~source_elpi:"graft_replace_ok.elpi"
  ~description:"replacing a clase"
    ()

let () = declare "graft_replace_err"
  ~source_elpi:"graft_replace_err.elpi"
  ~description:"replacing a clase"
    ~expectation:Test.(FailureOutput (Str.regexp "name attribute"))
  ()

let () = declare "graft_remove"
  ~source_elpi:"graft_remove.elpi"
  ~description:"remove a clase"
    ()


let () = declare "graft_before"
  ~source_elpi:"graft_before.elpi"
  ~description:"grafting a clause before the clause of another predicate"
    ()

let () = declare "graft_before_same"
  ~source_elpi:"graft_before_same.elpi"
  ~description:"grafting a clause before the clause of the same predicate"
    ()

let () = declare "mk_uv_meta"
  ~source_elpi:"mk-evar-meta.elpi"
  ~description:"uvar surgery at the meta level"
    ~expectation:Test.Success
  ()

let mk_tmp_file =
  let tmp = ref 0 in
  let dir = Filename.get_temp_dir_name () in
  fun x y ->
    incr tmp;
    dir ^ Filename.dir_sep ^ x ^ "__" ^ string_of_int !tmp ^ "__" ^ y
    
let () =
  let sample = mk_tmp_file "trace.json" ".new" in
  declare "trace-browser"
  ~source_elpi:"trace.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace.json" })
  ()

let sample = mk_tmp_file "trace.elab.json" ".new"
let () = declare "trace-browser-elab"
  ~source_json:"trace.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace.elab.json" })
  ()


let sample = mk_tmp_file "trace2.json" ".new"
let () = declare "trace-browser2"
  ~source_elpi:"trace2.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace2.json" })
  ()

let sample = mk_tmp_file "trace2.elab.json" ".new"
let () = declare "trace-browser2-elab"
  ~source_json:"trace2.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace2.elab.json" })
  ()

let sample = mk_tmp_file "trace3.json" ".new"
let () = declare "trace-browser3"
  ~source_elpi:"trace3.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace3.json" })
  ()

let sample = mk_tmp_file "trace3.elab.json" ".new"
let () = declare "trace-browser3-elab"
  ~source_json:"trace3.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace3.elab.json" })
  ()

let sample = mk_tmp_file "trace4.json" ".new"
let () = declare "trace-browser4"
  ~source_elpi:"trace4.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace4.json" })
  ()

let sample = mk_tmp_file "trace4.elab.json" ".new"
let () = declare "trace-browser4-elab"
  ~source_json:"trace4.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace4.elab.json" })
  ()
  

let sample = mk_tmp_file "trace_chr.json" ".new"
let () = declare "trace-browser-chr"
  ~source_elpi:"trace_chr.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_chr.json" })
  ()

let sample = mk_tmp_file "trace_chr.elab.json" ".new"
let () = declare "trace-browser-elab-chr"
  ~source_json:"trace_chr.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_chr.elab.json" })
  ()

let sample = mk_tmp_file "trace_findall.json" ".new"
let () = declare "trace-browser-findall"
  ~source_elpi:"trace_findall.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_findall.json" })
  ()

let sample = mk_tmp_file "trace_findall.elab.json" ".new"
let () = declare "trace-browser-elab-findall"
  ~source_json:"trace_findall.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_findall.elab.json" })
  ()

let sample = mk_tmp_file "trace_cut.json" ".new"
let () = declare "trace-browser-cut"
  ~source_elpi:"trace_cut.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_cut.json" })
  ()

let sample = mk_tmp_file "trace_cut.elab.json" ".new"
let () = declare "trace-browser-elab-cut"
  ~source_json:"trace_cut.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_cut.elab.json" })
  ()

let sample = Filename.temp_file "broken_trace1.elab.json" ".new"
let () = declare "trace-browser-elab-broken1"
  ~source_json:"broken_trace1.json"
  ~description:"recoverable broken trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "broken_trace1.elab.json" })
  ()
  
let sample = Filename.temp_file "broken_trace2.elab.json" ".new"
let () = declare "trace-browser-elab-broken2"
  ~source_json:"broken_trace2.json"
  ~description:"fatal broken trace elaboration"
  ~expectation:(FailureOutput (Str.regexp "broken.*step_id 217.*json object 1857"))
  ()
  

let () = declare "bad_index"
  ~source_elpi:"bad_index.elpi"
  ~description:"bad indexing directive"
  ~expectation:Test.(FailureOutput (Str.regexp "Wrong indexing"))
  ()
 

(* let sample = mk_tmp_file "trace_w.json" ".new"
let () = declare "trace-browser-w"
  ~source_elpi:"trace-w/main.elpi"
  ~description:"trace generation"
    ~trace:(On["json";"file://"^sample;"-trace-at";"0";"99";"-trace-only";"user"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_w.json" })
  () *)

let sample = mk_tmp_file "trace_w.elab.json" ".new"
let () = declare "trace-browser-w-elab"
  ~source_json:"trace_w.json"
  ~description:"trace elaboration"
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "trace_w.elab.json" })
  ()
  
  
let () = declare "impl_prec"
  ~source_elpi:"impl_prec.elpi"
  ~description:"warning about A => B, C"
  ~expectation:(SuccessOutput (Str.regexp "Warning.*line [12],"))
  ()
let () = declare "impl_prec_silent"
  ~source_elpi:"impl_prec_ok.elpi"
  ~description:"warning about A => B, C"
  ~expectation:(SuccessOutputTxt (fun l -> l|> List.for_all (fun l -> not @@ Str.string_match (Str.regexp "Warning,") l 0)))
  ()

let () = declare "ifdef"
~source_elpi:"ifdef.elpi"
~description:"lexer ifdef"
()