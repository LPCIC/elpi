#!/bin/bash

function provide() {
	local p="$1"
	ocamlfind query -qo $p 2>/dev/null || \
	test -d ${p}.*/ || \
	( echo "unpacking vendored ${p}"; tar -xzf ${p}.*.tgz )
}

provide seq
provide result
provide cppo
provide ppx_deriving
provide re