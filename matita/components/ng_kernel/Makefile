PACKAGE = ng_kernel
PREDICATES =

INTERFACE_FILES = \
	nUri.mli \
	nReference.mli \
	nCicUtils.mli \
	nCicSubstitution.mli \
	nCicEnvironment.mli \
	nCicReduction.mli \
        nCicELPI.mli \
	nCicTypeChecker.mli \
	nCicUntrusted.mli \
	nCicPp.mli

IMPLEMENTATION_FILES = \
  nCic.ml $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = 
EXTRA_OBJECTS_TO_CLEAN =
%.cmo: OCAMLOPTIONS += -w Ae
%.cmi: OCAMLOPTIONS += -w Ae
%.cmx: OCAMLOPTIONS += -w Ae

include ../../Makefile.defs
include ../Makefile.common

depend.dot: $(IMPLEMENTATION_FILES) $(INTERFACE_FILES)
	ocamldoc -o depend.dot -rectypes -I ../extlib/ -I ../cic -I ../cic_proof_checking/  -I ../urimanager/  -I ../logger/ -I ../registry/ -I ../getter/ -I ../hmysql/ -I ../library/ -I ../metadata/   -dot nUri.ml nReference.ml nCic.ml nCicPp.ml nCicEnvironment.ml nCicSubstitution.ml nCicReduction.ml nCicTypeChecker.ml nCicUtils.ml nCicLibrary.ml
	cat depend.dot | grep -v "^}$$" > /tmp/depend.dot && mv /tmp/depend.dot .
	for i in `cat depend.dot | grep darkturquoise | cut -d '"' -f 2`; do j=`echo $$i | sed s/^N/n/g`; size=`cat $$j.ml | wc -l`; funs=`cat $$j.mli | grep "^val " | wc -l`;  size=`expr $$size - 13`; echo "\"$$i\" [ label=\"$$i\\n$$size lines,\\n$$funs functions\"];"; done >> depend.dot
	echo "}" >> depend.dot
	cat depend.dot | grep -v "darkturquoise" > /tmp/depend.dot && mv /tmp/depend.dot .
	cat depend.dot
	tred < depend.dot > /tmp/depend.dot && mv /tmp/depend.dot .
	cat depend.dot | grep -v "^}$$" > /tmp/depend.dot && mv /tmp/depend.dot .
	echo "	NCicEnvironment -> NCicTypeChecker;" >> depend.dot
	cat depend.dot | grep -v "NCicEnvironment -> NCic;" > /tmp/depend.dot && mv /tmp/depend.dot .
	echo "NCicLibrary [ style=dashed ];" >> depend.dot
	echo "NCicPp [ style=dashed ];" >> depend.dot
	echo "}" >> depend.dot
	cat depend.dot | grep -v "rotate" > /tmp/depend.dot && mv /tmp/depend.dot .

depend.png depend.eps: depend.dot
	dot -Tpng > depend.png < depend.dot
	dot -Tps > depend.eps < depend.dot
