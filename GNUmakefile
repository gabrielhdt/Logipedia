DKCHECK = dkcheck
DKDEP   = dkdep

all: main.native

#### Main program ##################################################

main.native: _build/src/main.native

_build/src/main.native: $(wildcard src/*.ml src/*.mli)
	@echo "[OPT] main.native"
	@ocamlbuild -quiet -package dedukti.parser src/main.native

#### Producing the theory file #####################################

theories/sttfa.dko: theories/sttfa.dk
	@echo "[DKC] $^"
	@$(DKCHECK) -e $^

#### Running examples ##############################################

EXADKS = $(wildcard examples/*.dk)

examples: $(EXADKS:.dk=.stt) $(EXADKS:.dk=.pdf)

examples/%.dko examples/%.stt examples/%.tex: examples/%.dk theories/sttfa.dko main.native
	@echo "[STT] $<"
	@./main.native -I theories $<

examples/%.pdf: examples/%.tex
	@echo "[PDF] $@"
	@pdflatex -output-directory=examples $< > /dev/null || echo "ERROR on $@"

#### Producing the Dedukti library #################################

LIBDKS = $(wildcard library/*.dk)

library: $(LIBDKS:.dk=.dko) $(LIBDKS:.dk=.summary)

library/%.dko library/%.stt library/%.tex library/%.pvs: library/%.dk .library_depend main.native
	@echo "[STT,TEX,PVS] $<"
	@./main.native -I library -I theories $<

library/%.pdf: library/%.tex
	@echo "[PDF] $@"
	@pdflatex -halt-on-error -output-directory=library $< > /dev/null || echo "ERROR on $@"

.PRECIOUS: library/%.pvs

library/%.summary: library/%.pvs
	@echo "[SUMMARY]"
	touch $@

.library_depend: $(wildcard library/*.dk theories/*.dk examples/*.dk) 
	@echo "[DEP] $@"
	@$(DKDEP) -o $@ -I library -I theories $^

ifneq ($(MAKECMDGOALS), clean)
ifneq ($(MAKECMDGOALS), distclean)
-include .library_depend
endif
endif

#### Cleaning targets ##############################################

clean:
	@ocamlbuild -clean -quiet
	@rm -f .library_depend

distclean: clean
	@find . -name "*~" -exec rm {} \;
	@find . -name "*.dko" -exec rm {} \;
	@find library -name "*.stt" -exec rm {} \;
	@find library -name "*.aux" -exec rm {} \;
	@find library -name "*.log" -exec rm {} \;
	@find library -name "*.pdf" -exec rm {} \;
	@find library -name "*.tex" -exec rm {} \;
	@find library -name "*.pvs" -exec rm {} \;
	@find library -name "*.summary" -exec rm {} \;
	@find library -name ".pvs_context" -exec rm {} \;
	@find library -name "*.prf" -exec rm {} \;
	@find library/pvsbin -name "*.bin" -exec rm {} \;
	@find library/pvsbin -name "*.dep" -exec rm {} \;

.PHONY: all clean distclean examples library
