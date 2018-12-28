H = @

ENGINE = ld3_engine.elpi
EXPORT = export-lp2

ELPI       = ../../../elpi
HELENA_DIR = helena

TEMP = etc/temp.txt
TEST = etc/test_31.txt

all:

clean:
	$(H)$(RM) -f *~

test-tc:
	$(H)$(ELPI) -test $(ENGINE)

test:
	$(H)$(ELPI) -no-tc -test $(ENGINE)

test-31:
	$(H)mkdir -p etc 
	$(H)$(RM) $(TEMP)
	$(H)for RUN in `seq 1 31`; do $(ELPI) -no-tc -test $(ENGINE) 2>> $(TEMP); done
	$(H)echo `hostname` `date` > $(TEST)
	$(H)echo >> $(TEST)
	$(H)grep "Time: " $(TEMP) | sort -n -k 2 | cat -n >> $(TEST)

helena:
	$(H)$(MAKE) --no-print-directory -C $(HELENA_DIR) $(EXPORT)

.PHONY: helena
