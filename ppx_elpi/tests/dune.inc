
(rule
 (targets test_alias_type.actual.ml)
 (deps (:pp pp.exe) (:input test_alias_type.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_alias_type.expected.ml test_alias_type.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_alias_type.expected.elpi test_alias_type.actual.elpi)))

(rule
  (target test_alias_type.actual.elpi)
  (action (run ./test_alias_type.exe %{target})))

(executable
  (name test_alias_type)
  (modules test_alias_type)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_container.actual.ml)
 (deps (:pp pp.exe) (:input test_container.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_container.expected.ml test_container.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_container.expected.elpi test_container.actual.elpi)))

(rule
  (target test_container.actual.elpi)
  (action (run ./test_container.exe %{target})))

(executable
  (name test_container)
  (modules test_container)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_double_contextual.actual.ml)
 (deps (:pp pp.exe) (:input test_double_contextual.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_double_contextual.expected.ml test_double_contextual.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_double_contextual.expected.elpi test_double_contextual.actual.elpi)))

(rule
  (target test_double_contextual.actual.elpi)
  (action (run ./test_double_contextual.exe %{target})))

(executable
  (name test_double_contextual)
  (modules test_double_contextual)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_mutual_adt.actual.ml)
 (deps (:pp pp.exe) (:input test_mutual_adt.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_mutual_adt.expected.ml test_mutual_adt.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_mutual_adt.expected.elpi test_mutual_adt.actual.elpi)))

(rule
  (target test_mutual_adt.actual.elpi)
  (action (run ./test_mutual_adt.exe %{target})))

(executable
  (name test_mutual_adt)
  (modules test_mutual_adt)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_opaque_type.actual.ml)
 (deps (:pp pp.exe) (:input test_opaque_type.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_opaque_type.expected.ml test_opaque_type.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_opaque_type.expected.elpi test_opaque_type.actual.elpi)))

(rule
  (target test_opaque_type.actual.elpi)
  (action (run ./test_opaque_type.exe %{target})))

(executable
  (name test_opaque_type)
  (modules test_opaque_type)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_opaque_type_alias.actual.ml)
 (deps (:pp pp.exe) (:input test_opaque_type_alias.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_opaque_type_alias.expected.ml test_opaque_type_alias.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_opaque_type_alias.expected.elpi test_opaque_type_alias.actual.elpi)))

(rule
  (target test_opaque_type_alias.actual.elpi)
  (action (run ./test_opaque_type_alias.exe %{target})))

(executable
  (name test_opaque_type_alias)
  (modules test_opaque_type_alias)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_poly_adt.actual.ml)
 (deps (:pp pp.exe) (:input test_poly_adt.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_poly_adt.expected.ml test_poly_adt.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_poly_adt.expected.elpi test_poly_adt.actual.elpi)))

(rule
  (target test_poly_adt.actual.elpi)
  (action (run ./test_poly_adt.exe %{target})))

(executable
  (name test_poly_adt)
  (modules test_poly_adt)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_poly_alias.actual.ml)
 (deps (:pp pp.exe) (:input test_poly_alias.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_poly_alias.expected.ml test_poly_alias.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_poly_alias.expected.elpi test_poly_alias.actual.elpi)))

(rule
  (target test_poly_alias.actual.elpi)
  (action (run ./test_poly_alias.exe %{target})))

(executable
  (name test_poly_alias)
  (modules test_poly_alias)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_simple_adt.actual.ml)
 (deps (:pp pp.exe) (:input test_simple_adt.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_simple_adt.expected.ml test_simple_adt.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_simple_adt.expected.elpi test_simple_adt.actual.elpi)))

(rule
  (target test_simple_adt.actual.elpi)
  (action (run ./test_simple_adt.exe %{target})))

(executable
  (name test_simple_adt)
  (modules test_simple_adt)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_simple_adt_record.actual.ml)
 (deps (:pp pp.exe) (:input test_simple_adt_record.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_simple_adt_record.expected.ml test_simple_adt_record.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_simple_adt_record.expected.elpi test_simple_adt_record.actual.elpi)))

(rule
  (target test_simple_adt_record.actual.elpi)
  (action (run ./test_simple_adt_record.exe %{target})))

(executable
  (name test_simple_adt_record)
  (modules test_simple_adt_record)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_simple_contextual.actual.ml)
 (deps (:pp pp.exe) (:input test_simple_contextual.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_simple_contextual.expected.ml test_simple_contextual.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_simple_contextual.expected.elpi test_simple_contextual.actual.elpi)))

(rule
  (target test_simple_contextual.actual.elpi)
  (action (run ./test_simple_contextual.exe %{target})))

(executable
  (name test_simple_contextual)
  (modules test_simple_contextual)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_simple_record.actual.ml)
 (deps (:pp pp.exe) (:input test_simple_record.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_simple_record.expected.ml test_simple_record.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_simple_record.expected.elpi test_simple_record.actual.elpi)))

(rule
  (target test_simple_record.actual.elpi)
  (action (run ./test_simple_record.exe %{target})))

(executable
  (name test_simple_record)
  (modules test_simple_record)
  (preprocess (pps elpi.ppx)))


(rule
 (targets test_two_layers_context.actual.ml)
 (deps (:pp pp.exe) (:input test_two_layers_context.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_two_layers_context.expected.ml test_two_layers_context.actual.ml)))

(rule
 (alias runtest)
 (action (diff test_two_layers_context.expected.elpi test_two_layers_context.actual.elpi)))

(rule
  (target test_two_layers_context.actual.elpi)
  (action (run ./test_two_layers_context.exe %{target})))

(executable
  (name test_two_layers_context)
  (modules test_two_layers_context)
  (preprocess (pps elpi.ppx)))

