to compile elpi in bytecode, issue the command:

make CMX=cmo CMXA=cma OC="OCAMLPATH=$PWD ocamlfind ocamlc" OD="OCAMLPATH=$PWD ocamldep"
