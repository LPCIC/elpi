H        = @
XOA_DIR  = ../../../components/binaries/xoa
XOA      = xoa.native
DEP_DIR  = ../../../components/binaries/matitadep
DEP      = matitadep.native
MAC_DIR  = ../../../components/binaries/mac
MAC      = mac.native

XOA_CONF    = xoa.conf.xml
XOA_TARGETS = background/xoa_notation.ma background/xoa.ma

all: xoa
	$(H)../../matitac.opt */*.ma

# xoa ########################################################################

xoa: $(XOA_TARGETS)

$(XOA_TARGETS): $(XOA_CONF)
	@echo "  EXEC $(XOA) $(XOA_CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(XOA_CONF)

# dep ########################################################################

deps: MAS = $(shell find $* -name "*.ma")

deps: $(DEP_DIR)/$(DEP)
	@echo "  MATITADEP"
	$(H)grep "include \"" $(MAS) | $<
