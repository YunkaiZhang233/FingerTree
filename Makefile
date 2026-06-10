.PHONY: all install coq clean clean_coq audit

all: coq

# Mechanical realisation of the thesis contribution audit: rejects any
# Admitted/admit/Axiom in src/Finger*.v and runs Print Assumptions on the
# headline theorems (src/Audit.v), allowing only Classical_Prop.classic.
audit: coq
	./scripts/audit.sh

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq

clean_coq: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall

clean: clean_coq
	$(RM) Makefile.coq
	$(RM) Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@
