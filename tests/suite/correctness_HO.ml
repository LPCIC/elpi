(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "ho"
  ~source_elpi:"ho.elpi"
  ~description:"HO predicates"
  ()
let () = declare "hc_interp"
  ~source_elpi:"hc_interp.elpi"
  ~description:"Horn Clauses interpreter"
  ()


let () = declare "eta"
  ~source_elpi:"eta.elpi"
  ~description:"test eta for rigid terms"
  ()

let () = declare "beta"
  ~source_elpi:"beta.elpi"
  ~description:"beta reduction"
  ()

let () = declare "pi"
  ~source_elpi:"pi.elpi"
  ~description:"pi quantification"
  ()
let () = declare "pi3"
  ~source_elpi:"pi3.elpi"
  ~description:"pi quantification"
  ()
let () = declare "pi5"
  ~source_elpi:"pi5.elpi"
  ~description:"pi quantification"
  ()

let () = declare "impl"
  ~source_elpi:"impl.elpi"
  ~description:"implication"
  ()
let () = declare "impl2"
  ~source_elpi:"impl2.elpi"
  ~description:"implication"
  ()

let () = declare "patternunif"
  ~source_elpi:"patternunif.elpi"
  ~description:"Miller pattern unification"
  ()
let () = declare "patternunif2"
  ~source_elpi:"patternunif2.elpi"
  ~description:"Miller pattern unification"
  ()
let () = declare "self_assignment"
  ~source_elpi:"self_assignment.elpi"
  ~description:"Miller pattern unification"
  ()
let () = declare "llam"
  ~source_elpi:"llam.elpi"
  ~source_teyjus:"llam.mod"
  ~description:"Miller pattern unification"
  ()
let () = declare "llamb0_exit1"
  ~source_elpi:"fragment_exit.elpi"
  ~description:"Outside the llamb0 fragment"
  ()
let () = declare "llamb0_exit2"
  ~source_elpi:"fragment_exit2.elpi"
  ~description:"Outside the llamb0 fragment"
  ()
let () = declare "llamb0_exit3"
  ~source_elpi:"fragment_exit3.elpi"
  ~description:"Outside the llamb0 fragment"
  ()
let () = declare "llamb0_exit4"
  ~source_elpi:"general_case.elpi"
  ~description:"Outside the llamb0 fragment"
  ()
let () = declare "llamb0_exit5"
  ~source_elpi:"general_case2.elpi"
  ~description:"Outside the llamb0 fragment"
  ()
let () = declare "llamb0_exit6"
  ~source_elpi:"general_case3.elpi"
  ~description:"Outside the llamb0 fragment"
  ()

let () = declare "restriction3"
  ~source_elpi:"restriction3.elpi"
  ~description:"HO unification scope checking"
  ()
let () = declare "restriction4"
  ~source_elpi:"restriction4.elpi"
  ~description:"HO unification scope checking"
  ()
let () = declare "restriction5"
  ~source_elpi:"restriction5.elpi"
  ~description:"HO unification scope checking"
  ()
let () = declare "restriction6"
  ~source_elpi:"restriction6.elpi"
  ~description:"HO unification scope checking"
  ()
let () = declare "restriction"
  ~source_elpi:"restriction.elpi"
  ~description:"HO unification scope checking"
  ~expectation:Test.Failure
  ()

let () = declare "bug19"
  ~source_elpi:"GH_issue_19.elpi"
  ~description:"unif under binders"
  ()

let () = declare "lambdadelta"
  ~source_elpi:"helena_elpi/lambdadelta.elpi"
  ~description:"lambda delta tests"
  ()

let () = declare "notation"
  ~source_elpi:"notation.elpi"
  ~description:"extensible syntax"
  ()

let () = declare "notation_legacy"
  ~source_elpi:"notation_legacy.elpi"
  ~legacy_parser:true
  ~description:"extensible syntax"
  ()

let () = declare "pnf"
  ~source_elpi:"pnf.elpi"
  ~description:"some HO programming"
  ()

let () = declare "holp"
  ~source_elpi:"holp/main.mod"
  ~source_teyjus:"holp/main.mod"
  ~deps_teyjus:[
    "holp/hcinterp_examples.mod";
    "holp/hc_syntax.mod";
    "holp/pnf_examples.mod";
    "holp/hc_interp.mod";
    "holp/lists.mod";
    "holp/pnf.mod";
    "holp/hcsyntax_examples.mod";
    "holp/refl_syntax.mod";
  ]
  ~description:"HOL programming"
  ()

  let () = declare "holp_legacy"
  ~source_elpi:"holp_legacy/main.mod"
  ~source_teyjus:"holp_legacy/main.mod"
  ~deps_teyjus:[
    "holp_legacy/hcinterp_examples.mod";
    "holp_legacy/hc_syntax.mod";
    "holp_legacy/pnf_examples.mod";
    "holp_legacy/hc_interp.mod";
    "holp_legacy/lists.mod";
    "holp_legacy/pnf.mod";
    "holp_legacy/hcsyntax_examples.mod";
    "holp_legacy/refl_syntax.mod";
  ]
  ~legacy_parser:true
  ~description:"HOL programming"
  ()

let () = declare "ndprover"
  ~source_elpi:"ndprover/inter.mod"
  ~source_teyjus:"ndprover/inter.mod"
  ~deps_teyjus:[
    "ndprover/formulas.mod";
    "ndprover/ndtac.mod";
    "ndprover/goalred.mod";
    "ndprover/listmanip.mod";
    "ndprover/tacticals.mod";
  ]
  ~input:"ndprover.stdin"
  ~description:"Natural deduction prover"
  ()

  let () = declare "ndprover_legacy"
  ~source_elpi:"ndprover_legacy/inter.mod"
  ~source_teyjus:"ndprover_legacy/inter.mod"
  ~deps_teyjus:[
    "ndprover_legacy/formulas.mod";
    "ndprover_legacy/ndtac.mod";
    "ndprover_legacy/goalred.mod";
    "ndprover_legacy/listmanip.mod";
    "ndprover_legacy/tacticals.mod";
  ]
  ~input:"ndprover.stdin"
  ~description:"Natural deduction prover"
  ~legacy_parser:true
  ()

let () = declare "pcf"
  ~source_elpi:"pcf/pcf.mod"
  ~source_teyjus:"pcf/pcf.mod"
  ~deps_teyjus:[
    "pcf/control.mod";
    "pcf/monoinfer.mod";
    "pcf/poly_test.mod";
    "pcf/unifytypes.mod";
    "pcf/eval.mod";
    "pcf/mono_test.mod";
    "pcf/refl_syntax.mod";
    "pcf/eval_test.mod";
    "pcf/tailrec.mod";
    "pcf/examples.mod";
    "pcf/polyinfer.mod";
    "pcf/tr_test.mod";
  ]
  ~description:"type inference for PCF"
  ()

let () = declare "pcf_legacy"
  ~source_elpi:"pcf_legacy/pcf.mod"
  ~source_teyjus:"pcf_legacy/pcf.mod"
  ~deps_teyjus:[
    "pcf_legacy/control.mod";
    "pcf_legacy/monoinfer.mod";
    "pcf_legacy/poly_test.mod";
    "pcf_legacy/unifytypes.mod";
    "pcf_legacy/eval.mod";
    "pcf_legacy/mono_test.mod";
    "pcf_legacy/refl_syntax.mod";
    "pcf_legacy/eval_test.mod";
    "pcf_legacy/tailrec.mod";
    "pcf_legacy/examples.mod";
    "pcf_legacy/polyinfer.mod";
    "pcf_legacy/tr_test.mod";
  ]
  ~description:"type inference for PCF"
  ~legacy_parser:true
  ()

let () = declare "progs"
  ~source_elpi:"progs/progs.mod"
  ~source_teyjus:"progs/progs.mod"
  ~deps_teyjus:[
    "progs/curry_test.mod";
    "progs/eval_basic.mod";
    "progs/eval.mod";
    "progs/progs1.mod";
    "progs/progs3.mod";
    "progs/terms.mod";
    "progs/tr2_test.mod";
    "progs/curry_transform.mod";
    "progs/eval_examples.mod";
    "progs/general_tr.mod";
    "progs/progs2.mod";
    "progs/progs4.mod";
    "progs/refl_syntax.mod";
    "progs/tr1_test.mod";
    "progs/tr_recognizer.mod";
  ]
  ~description:"progs"
  ~outside_llam:true
  ()

let () = declare "lambda_arrow1"
  ~source_elpi:"lambda.elpi"
  ~description:"simple type checker"
  ()

let () = declare "lambda_arrow2"
  ~source_elpi:"lambda2.elpi"
  ~description:"simple type checker"
  ()

let () = declare "hilbert"
  ~source_elpi:"hilbert/hilbert.mod"
  ~source_teyjus:"hilbert/hilbert.mod"
  ~description:"hilbert"
  ~outside_llam:true
  ()
let () = declare "hilbert2"
  ~source_elpi:"hilbert2/hilbert2.mod"
  ~source_teyjus:"hilbert2/hilbert2.mod"
  ~description:"hilbert2"
  ~outside_llam:true
  ()

let () = declare "eta_as"
  ~source_elpi:"eta_as.elpi"
  ~description:"eta expansion of as clause"
  ~typecheck:false
  ()

let () = declare "hdclause"
  ~source_elpi:"hdclause.elpi"
  ~description:"hdclause unification"
  ~typecheck:false
  ()
  
let () = declare "oc_eta"
  ~source_elpi:"oc_eta.elpi"
  ~description:"eta expansion and occur check"
  ~typecheck:true
  ~expectation:Failure
  ()

let () = declare "eta_oc"
  ~source_elpi:"eta_oc.elpi"
  ~description:"eta expansion and occur check"
  ~typecheck:true
  ~expectation:Success
  ()
  
let () = declare "bug_226"
  ~source_elpi:"bug_226.elpi"
  ~description:"move/unif bug"
  ~typecheck:true
  ~expectation:Success
  ()

let () = declare "chr-scope"
  ~source_elpi:"chr-scope.elpi"
  ~description:"chr-relocation"
  ~typecheck:true
  ~expectation:Success
  ()

let () = declare "chr-scope-change"
  ~source_elpi:"chr-scope-change.elpi"
  ~description:"chr-relocation"
  ~typecheck:true
  ~expectation:Success
  ()

let () = declare "chr-scope-change-err"
  ~source_elpi:"chr-scope-change-failure.elpi"
  ~description:"chr-relocation"
  ~typecheck:true
  ~expectation:(FailureOutput (Str.regexp "cannot be put in the desired context"))
  ()

let () = declare "chr_with_hypotheses"
  ~source_elpi:"chr_with_hypotheses.elpi"
  ~description:"chr_with_hypotheses"
  ~typecheck:true
  ~expectation:Success
  ()

let () = declare "bug_272"
  ~source_elpi:"dt_bug272.elpi"
  ~description:"dt list truncation heuristic"
  ~typecheck:true
  ~expectation:Success
  ()

