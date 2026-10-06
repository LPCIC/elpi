
; The output of the ppx and of the test executable is generated in
; test_alias_type.generated.* and compared with test_alias_type.expected.*, but it is also promoted
; to test_alias_type.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_alias_type.generated.ml)
 (deps (:pp pp.exe) (:input test_alias_type.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_alias_type.generated.elpi)
 (action (run ./test_alias_type.exe %{target})))

(rule
 (mode promote)
 (target test_alias_type.actual.ml)
 (action (copy test_alias_type.generated.ml test_alias_type.actual.ml)))

(rule
 (mode promote)
 (target test_alias_type.actual.elpi)
 (action (copy test_alias_type.generated.elpi test_alias_type.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_alias_type.actual.ml test_alias_type.actual.elpi)
 (action (diff test_alias_type.expected.ml test_alias_type.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_alias_type.expected.elpi test_alias_type.generated.elpi)))

(executable
  (name test_alias_type)
  (modules test_alias_type)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_attributes.generated.* and compared with test_attributes.expected.*, but it is also promoted
; to test_attributes.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_attributes.generated.ml)
 (deps (:pp pp.exe) (:input test_attributes.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_attributes.generated.elpi)
 (action (run ./test_attributes.exe %{target})))

(rule
 (mode promote)
 (target test_attributes.actual.ml)
 (action (copy test_attributes.generated.ml test_attributes.actual.ml)))

(rule
 (mode promote)
 (target test_attributes.actual.elpi)
 (action (copy test_attributes.generated.elpi test_attributes.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_attributes.actual.ml test_attributes.actual.elpi)
 (action (diff test_attributes.expected.ml test_attributes.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_attributes.expected.elpi test_attributes.generated.elpi)))

(executable
  (name test_attributes)
  (modules test_attributes)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_compose_contextual.generated.* and compared with test_compose_contextual.expected.*, but it is also promoted
; to test_compose_contextual.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_compose_contextual.generated.ml)
 (deps (:pp pp.exe) (:input test_compose_contextual.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_compose_contextual.generated.elpi)
 (action (run ./test_compose_contextual.exe %{target})))

(rule
 (mode promote)
 (target test_compose_contextual.actual.ml)
 (action (copy test_compose_contextual.generated.ml test_compose_contextual.actual.ml)))

(rule
 (mode promote)
 (target test_compose_contextual.actual.elpi)
 (action (copy test_compose_contextual.generated.elpi test_compose_contextual.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_compose_contextual.actual.ml test_compose_contextual.actual.elpi)
 (action (diff test_compose_contextual.expected.ml test_compose_contextual.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_compose_contextual.expected.elpi test_compose_contextual.generated.elpi)))

(executable
  (name test_compose_contextual)
  (modules test_compose_contextual)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_container.generated.* and compared with test_container.expected.*, but it is also promoted
; to test_container.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_container.generated.ml)
 (deps (:pp pp.exe) (:input test_container.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_container.generated.elpi)
 (action (run ./test_container.exe %{target})))

(rule
 (mode promote)
 (target test_container.actual.ml)
 (action (copy test_container.generated.ml test_container.actual.ml)))

(rule
 (mode promote)
 (target test_container.actual.elpi)
 (action (copy test_container.generated.elpi test_container.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_container.actual.ml test_container.actual.elpi)
 (action (diff test_container.expected.ml test_container.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_container.expected.elpi test_container.generated.elpi)))

(executable
  (name test_container)
  (modules test_container)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_copy_aliases_opaque.generated.* and compared with test_copy_aliases_opaque.expected.*, but it is also promoted
; to test_copy_aliases_opaque.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_copy_aliases_opaque.generated.ml)
 (deps (:pp pp.exe) (:input test_copy_aliases_opaque.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_copy_aliases_opaque.generated.elpi)
 (action (run ./test_copy_aliases_opaque.exe %{target})))

(rule
 (mode promote)
 (target test_copy_aliases_opaque.actual.ml)
 (action (copy test_copy_aliases_opaque.generated.ml test_copy_aliases_opaque.actual.ml)))

(rule
 (mode promote)
 (target test_copy_aliases_opaque.actual.elpi)
 (action (copy test_copy_aliases_opaque.generated.elpi test_copy_aliases_opaque.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_copy_aliases_opaque.actual.ml test_copy_aliases_opaque.actual.elpi)
 (action (diff test_copy_aliases_opaque.expected.ml test_copy_aliases_opaque.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_copy_aliases_opaque.expected.elpi test_copy_aliases_opaque.generated.elpi)))

(executable
  (name test_copy_aliases_opaque)
  (modules test_copy_aliases_opaque)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_double_contextual.generated.* and compared with test_double_contextual.expected.*, but it is also promoted
; to test_double_contextual.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_double_contextual.generated.ml)
 (deps (:pp pp.exe) (:input test_double_contextual.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_double_contextual.generated.elpi)
 (action (run ./test_double_contextual.exe %{target})))

(rule
 (mode promote)
 (target test_double_contextual.actual.ml)
 (action (copy test_double_contextual.generated.ml test_double_contextual.actual.ml)))

(rule
 (mode promote)
 (target test_double_contextual.actual.elpi)
 (action (copy test_double_contextual.generated.elpi test_double_contextual.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_double_contextual.actual.ml test_double_contextual.actual.elpi)
 (action (diff test_double_contextual.expected.ml test_double_contextual.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_double_contextual.expected.elpi test_double_contextual.generated.elpi)))

(executable
  (name test_double_contextual)
  (modules test_double_contextual)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_mutual_adt.generated.* and compared with test_mutual_adt.expected.*, but it is also promoted
; to test_mutual_adt.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_mutual_adt.generated.ml)
 (deps (:pp pp.exe) (:input test_mutual_adt.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_mutual_adt.generated.elpi)
 (action (run ./test_mutual_adt.exe %{target})))

(rule
 (mode promote)
 (target test_mutual_adt.actual.ml)
 (action (copy test_mutual_adt.generated.ml test_mutual_adt.actual.ml)))

(rule
 (mode promote)
 (target test_mutual_adt.actual.elpi)
 (action (copy test_mutual_adt.generated.elpi test_mutual_adt.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_mutual_adt.actual.ml test_mutual_adt.actual.elpi)
 (action (diff test_mutual_adt.expected.ml test_mutual_adt.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_mutual_adt.expected.elpi test_mutual_adt.generated.elpi)))

(executable
  (name test_mutual_adt)
  (modules test_mutual_adt)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_opaque_type.generated.* and compared with test_opaque_type.expected.*, but it is also promoted
; to test_opaque_type.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_opaque_type.generated.ml)
 (deps (:pp pp.exe) (:input test_opaque_type.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_opaque_type.generated.elpi)
 (action (run ./test_opaque_type.exe %{target})))

(rule
 (mode promote)
 (target test_opaque_type.actual.ml)
 (action (copy test_opaque_type.generated.ml test_opaque_type.actual.ml)))

(rule
 (mode promote)
 (target test_opaque_type.actual.elpi)
 (action (copy test_opaque_type.generated.elpi test_opaque_type.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_opaque_type.actual.ml test_opaque_type.actual.elpi)
 (action (diff test_opaque_type.expected.ml test_opaque_type.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_opaque_type.expected.elpi test_opaque_type.generated.elpi)))

(executable
  (name test_opaque_type)
  (modules test_opaque_type)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_opaque_type_alias.generated.* and compared with test_opaque_type_alias.expected.*, but it is also promoted
; to test_opaque_type_alias.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_opaque_type_alias.generated.ml)
 (deps (:pp pp.exe) (:input test_opaque_type_alias.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_opaque_type_alias.generated.elpi)
 (action (run ./test_opaque_type_alias.exe %{target})))

(rule
 (mode promote)
 (target test_opaque_type_alias.actual.ml)
 (action (copy test_opaque_type_alias.generated.ml test_opaque_type_alias.actual.ml)))

(rule
 (mode promote)
 (target test_opaque_type_alias.actual.elpi)
 (action (copy test_opaque_type_alias.generated.elpi test_opaque_type_alias.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_opaque_type_alias.actual.ml test_opaque_type_alias.actual.elpi)
 (action (diff test_opaque_type_alias.expected.ml test_opaque_type_alias.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_opaque_type_alias.expected.elpi test_opaque_type_alias.generated.elpi)))

(executable
  (name test_opaque_type_alias)
  (modules test_opaque_type_alias)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_poly_adt.generated.* and compared with test_poly_adt.expected.*, but it is also promoted
; to test_poly_adt.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_poly_adt.generated.ml)
 (deps (:pp pp.exe) (:input test_poly_adt.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_poly_adt.generated.elpi)
 (action (run ./test_poly_adt.exe %{target})))

(rule
 (mode promote)
 (target test_poly_adt.actual.ml)
 (action (copy test_poly_adt.generated.ml test_poly_adt.actual.ml)))

(rule
 (mode promote)
 (target test_poly_adt.actual.elpi)
 (action (copy test_poly_adt.generated.elpi test_poly_adt.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_poly_adt.actual.ml test_poly_adt.actual.elpi)
 (action (diff test_poly_adt.expected.ml test_poly_adt.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_poly_adt.expected.elpi test_poly_adt.generated.elpi)))

(executable
  (name test_poly_adt)
  (modules test_poly_adt)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_poly_alias.generated.* and compared with test_poly_alias.expected.*, but it is also promoted
; to test_poly_alias.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_poly_alias.generated.ml)
 (deps (:pp pp.exe) (:input test_poly_alias.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_poly_alias.generated.elpi)
 (action (run ./test_poly_alias.exe %{target})))

(rule
 (mode promote)
 (target test_poly_alias.actual.ml)
 (action (copy test_poly_alias.generated.ml test_poly_alias.actual.ml)))

(rule
 (mode promote)
 (target test_poly_alias.actual.elpi)
 (action (copy test_poly_alias.generated.elpi test_poly_alias.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_poly_alias.actual.ml test_poly_alias.actual.elpi)
 (action (diff test_poly_alias.expected.ml test_poly_alias.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_poly_alias.expected.elpi test_poly_alias.generated.elpi)))

(executable
  (name test_poly_alias)
  (modules test_poly_alias)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_simple_adt.generated.* and compared with test_simple_adt.expected.*, but it is also promoted
; to test_simple_adt.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_simple_adt.generated.ml)
 (deps (:pp pp.exe) (:input test_simple_adt.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_simple_adt.generated.elpi)
 (action (run ./test_simple_adt.exe %{target})))

(rule
 (mode promote)
 (target test_simple_adt.actual.ml)
 (action (copy test_simple_adt.generated.ml test_simple_adt.actual.ml)))

(rule
 (mode promote)
 (target test_simple_adt.actual.elpi)
 (action (copy test_simple_adt.generated.elpi test_simple_adt.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_simple_adt.actual.ml test_simple_adt.actual.elpi)
 (action (diff test_simple_adt.expected.ml test_simple_adt.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_simple_adt.expected.elpi test_simple_adt.generated.elpi)))

(executable
  (name test_simple_adt)
  (modules test_simple_adt)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_simple_adt_record.generated.* and compared with test_simple_adt_record.expected.*, but it is also promoted
; to test_simple_adt_record.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_simple_adt_record.generated.ml)
 (deps (:pp pp.exe) (:input test_simple_adt_record.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_simple_adt_record.generated.elpi)
 (action (run ./test_simple_adt_record.exe %{target})))

(rule
 (mode promote)
 (target test_simple_adt_record.actual.ml)
 (action (copy test_simple_adt_record.generated.ml test_simple_adt_record.actual.ml)))

(rule
 (mode promote)
 (target test_simple_adt_record.actual.elpi)
 (action (copy test_simple_adt_record.generated.elpi test_simple_adt_record.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_simple_adt_record.actual.ml test_simple_adt_record.actual.elpi)
 (action (diff test_simple_adt_record.expected.ml test_simple_adt_record.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_simple_adt_record.expected.elpi test_simple_adt_record.generated.elpi)))

(executable
  (name test_simple_adt_record)
  (modules test_simple_adt_record)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_simple_contextual.generated.* and compared with test_simple_contextual.expected.*, but it is also promoted
; to test_simple_contextual.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_simple_contextual.generated.ml)
 (deps (:pp pp.exe) (:input test_simple_contextual.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_simple_contextual.generated.elpi)
 (action (run ./test_simple_contextual.exe %{target})))

(rule
 (mode promote)
 (target test_simple_contextual.actual.ml)
 (action (copy test_simple_contextual.generated.ml test_simple_contextual.actual.ml)))

(rule
 (mode promote)
 (target test_simple_contextual.actual.elpi)
 (action (copy test_simple_contextual.generated.elpi test_simple_contextual.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_simple_contextual.actual.ml test_simple_contextual.actual.elpi)
 (action (diff test_simple_contextual.expected.ml test_simple_contextual.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_simple_contextual.expected.elpi test_simple_contextual.generated.elpi)))

(executable
  (name test_simple_contextual)
  (modules test_simple_contextual)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_simple_contextual_key_last.generated.* and compared with test_simple_contextual_key_last.expected.*, but it is also promoted
; to test_simple_contextual_key_last.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_simple_contextual_key_last.generated.ml)
 (deps (:pp pp.exe) (:input test_simple_contextual_key_last.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_simple_contextual_key_last.generated.elpi)
 (action (run ./test_simple_contextual_key_last.exe %{target})))

(rule
 (mode promote)
 (target test_simple_contextual_key_last.actual.ml)
 (action (copy test_simple_contextual_key_last.generated.ml test_simple_contextual_key_last.actual.ml)))

(rule
 (mode promote)
 (target test_simple_contextual_key_last.actual.elpi)
 (action (copy test_simple_contextual_key_last.generated.elpi test_simple_contextual_key_last.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_simple_contextual_key_last.actual.ml test_simple_contextual_key_last.actual.elpi)
 (action (diff test_simple_contextual_key_last.expected.ml test_simple_contextual_key_last.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_simple_contextual_key_last.expected.elpi test_simple_contextual_key_last.generated.elpi)))

(executable
  (name test_simple_contextual_key_last)
  (modules test_simple_contextual_key_last)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_simple_record.generated.* and compared with test_simple_record.expected.*, but it is also promoted
; to test_simple_record.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_simple_record.generated.ml)
 (deps (:pp pp.exe) (:input test_simple_record.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_simple_record.generated.elpi)
 (action (run ./test_simple_record.exe %{target})))

(rule
 (mode promote)
 (target test_simple_record.actual.ml)
 (action (copy test_simple_record.generated.ml test_simple_record.actual.ml)))

(rule
 (mode promote)
 (target test_simple_record.actual.elpi)
 (action (copy test_simple_record.generated.elpi test_simple_record.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_simple_record.actual.ml test_simple_record.actual.elpi)
 (action (diff test_simple_record.expected.ml test_simple_record.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_simple_record.expected.elpi test_simple_record.generated.elpi)))

(executable
  (name test_simple_record)
  (modules test_simple_record)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_two_binders.generated.* and compared with test_two_binders.expected.*, but it is also promoted
; to test_two_binders.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_two_binders.generated.ml)
 (deps (:pp pp.exe) (:input test_two_binders.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_two_binders.generated.elpi)
 (action (run ./test_two_binders.exe %{target})))

(rule
 (mode promote)
 (target test_two_binders.actual.ml)
 (action (copy test_two_binders.generated.ml test_two_binders.actual.ml)))

(rule
 (mode promote)
 (target test_two_binders.actual.elpi)
 (action (copy test_two_binders.generated.elpi test_two_binders.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_two_binders.actual.ml test_two_binders.actual.elpi)
 (action (diff test_two_binders.expected.ml test_two_binders.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_two_binders.expected.elpi test_two_binders.generated.elpi)))

(executable
  (name test_two_binders)
  (modules test_two_binders)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_two_layers_context.generated.* and compared with test_two_layers_context.expected.*, but it is also promoted
; to test_two_layers_context.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_two_layers_context.generated.ml)
 (deps (:pp pp.exe) (:input test_two_layers_context.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_two_layers_context.generated.elpi)
 (action (run ./test_two_layers_context.exe %{target})))

(rule
 (mode promote)
 (target test_two_layers_context.actual.ml)
 (action (copy test_two_layers_context.generated.ml test_two_layers_context.actual.ml)))

(rule
 (mode promote)
 (target test_two_layers_context.actual.elpi)
 (action (copy test_two_layers_context.generated.elpi test_two_layers_context.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_two_layers_context.actual.ml test_two_layers_context.actual.elpi)
 (action (diff test_two_layers_context.expected.ml test_two_layers_context.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_two_layers_context.expected.elpi test_two_layers_context.generated.elpi)))

(executable
  (name test_two_layers_context)
  (modules test_two_layers_context)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))


; The output of the ppx and of the test executable is generated in
; test_variant.generated.* and compared with test_variant.expected.*, but it is also promoted
; to test_variant.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets test_variant.generated.ml)
 (deps (:pp pp.exe) (:input test_variant.ml))
 (action (run ./%{pp} -deriving-keep-w32 both --impl %{input} -o %{targets})))

(rule
 (target test_variant.generated.elpi)
 (action (run ./test_variant.exe %{target})))

(rule
 (mode promote)
 (target test_variant.actual.ml)
 (action (copy test_variant.generated.ml test_variant.actual.ml)))

(rule
 (mode promote)
 (target test_variant.actual.elpi)
 (action (copy test_variant.generated.elpi test_variant.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps test_variant.actual.ml test_variant.actual.elpi)
 (action (diff test_variant.expected.ml test_variant.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff test_variant.expected.elpi test_variant.generated.elpi)))

(executable
  (name test_variant)
  (modules test_variant)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))

