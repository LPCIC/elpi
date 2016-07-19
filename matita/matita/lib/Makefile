#TARGET= extraction2.ma
#TARGET= extraction3.ma
#TARGET= basics/logic.ma
#TARGET= basics/types.ma
#TARGET= basics/deqsets.ma
#TARGET= basics/lists/list.ma
#TARGET= arithmetics/nat.ma
TARGET= turing/multi_universal/universal.ma

all:
	touch $(TARGET)
	#EXTRACT_HASKELL=1 ../matitac $(TARGET) 2> /tmp/foo.hs
	#cat preamble.hs /tmp/foo.hs > extraction.hs
	EXTRACT_OCAML=1 ../matitac $(TARGET)

opt:
	touch $(TARGET)
	#EXTRACT_HASKELL=1 ../matitac.opt $(TARGET) 2> /tmp/foo.hs
	#cat preamble.hs /tmp/foo.hs > extraction.hs
	EXTRACT_OCAML=1 ../matitac.opt $(TARGET)

.PHONY: all opt

# ghci extraction.hs
# Syntax for datatypes: data Foo = Zero | Succ Foo Foo
