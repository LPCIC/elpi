H = @

ELPI       = ../../../elpi
HELENA_DIR = helena

TEMP = etc/temp.txt
TEST = etc/test_31.txt

all:

clean:
	$(H)$(RM) -f *~

test-tc:
	$(H)$(ELPI) -test lyp_engine.elpi

test:
	$(H)$(ELPI) -no-tc -test lyp_engine.elpi

test-31:
	$(H)mkdir -p etc 
	$(H)$(RM) $(TEMP)
	$(H)for RUN in `seq 1 31`; do $(ELPI) -no-tc -test lyp_engine.elpi 2>> $(TEMP); done
	$(H)echo `hostname` `date` > $(TEST)
	$(H)echo >> $(TEST)
	$(H)grep "Time: " $(TEMP) | sort -n -k 2 | cat -n >> $(TEST)

helena:
	$(H)$(MAKE) --no-print-directory -C $(HELENA_DIR) export-lyp

.PHONY: helena
