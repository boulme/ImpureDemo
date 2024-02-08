.PHONY: debug clean cleanall

SRCD:=../coq_src

OCB:=ocamlbuild -I coq_extracted -I ImpureOracles -lib unix

debug: coq_extracted
	$(OCB) -cflag -g -lflag -g FixTypeSafety.byte
	OCAMLRUNPARAM=b ./FixTypeSafety.byte || echo

# Auxiliary defs

$(SRCD)/Makefile: $(SRCD)/_CoqProject
	cd $(SRCD); coq_makefile -f _CoqProject -o Makefile

$(SRCD)/Impure/ImpExtern.vo: $(SRCD)/Makefile $(SRCD)/Impure/*.v 
	$(MAKE) -C $(SRCD) -j Impure/ImpExtern.vo

$(SRCD)/FixTypeSafety.vo coq_extracted: Makefile $(SRCD)/Impure/ImpExtern.vo $(SRCD)/FixTypeSafety.v
	rm -rf coq_extracted && mkdir coq_extracted && cd coq_extracted && coqc  -R ../$(SRCD) "ImpureDemo" -I ../$(SRCD) ../$(SRCD)/FixTypeSafety.v

clean:
	$(OCB) -clean
	rm -rf coq_extracted *~

cleanall: clean
	$(MAKE) -C $(SRCD) cleanall
	rm -rf $(SRCD)/Makefile* $(SRCD)/*.vo $(SRCD)/*.d $(SRCD)/*.glob $(SRCD)/.*.aux
