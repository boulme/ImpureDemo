.PHONY: debug run clean cleanall

SRCD:=../coq_src

OCB:=ocamlbuild -I coq_extracted -I ImpureOracles -lib unix

run: coq_extracted
	$(OCB) FibExample.native
	./FibExample.native || echo

debug: coq_extracted
	$(OCB) -cflag -g -lflag -g FibExample.byte
	OCAMLRUNPARAM=b	./FibExample.byte || echo

# Auxiliary defs

$(SRCD)/Makefile: $(SRCD)/_CoqProject
	cd $(SRCD); coq_makefile -f _CoqProject -o Makefile

$(SRCD)/Impure/ImpExtern.vo: $(SRCD)/Makefile $(SRCD)/Impure/*.v 
	$(MAKE) -C $(SRCD) -j Impure/ImpExtern.vo

$(SRCD)/FibExample.vo coq_extracted: Makefile $(SRCD)/Impure/ImpExtern.vo $(SRCD)/FibExample.v
	rm -rf coq_extracted && mkdir coq_extracted && cd coq_extracted && coqc  -R ../$(SRCD) "ImpureDemo" -I ../$(SRCD) ../$(SRCD)/FibExample.v

clean:
	$(OCB) -clean
	rm -rf coq_extracted *~

cleanall: clean
	$(MAKE) -C $(SRCD) cleanall
	rm -rf $(SRCD)/Makefile* $(SRCD)/*.vo $(SRCD)/*.d $(SRCD)/*.glob $(SRCD)/.*.aux
