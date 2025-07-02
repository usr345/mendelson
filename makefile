OUTPUT=$(shell which rocq 2>/dev/null)

# COQC=rocq c -R . Mendelson
# COQC=coqc -R . Mendelson
# rocq
ifneq ($(OUTPUT), "")
	COQC=rocq c
else
	COQC=coqc
endif

COQC := $(COQC)" -R . Mendelson"
all:
	@echo [$(COQC)]
	@echo [$(OUTPUT)]

#Meta.vo

FSignature.vo : FSignature.v
	$(COQC) FSignature.v

Sets.vo : Sets.v
	$(COQC) Sets.v

Formula.vo : Formula.v FSignature.vo
	$(COQC) Formula.v

Semantic.vo : Semantic.v Sets.vo Formula.vo
	$(COQC) Semantic.v

Syntactic.vo : Syntactic.v Sets.vo Formula.vo
	$(COQC) Syntactic.v

EqDec.vo : EqDec.v
	$(COQC) EqDec.v

Meta.vo : Meta.v Syntactic.vo Semantic.vo EqDec.vo
	$(COQC) Meta.v

L1_Hilbert_Accerman.vo : L1_Hilbert_Accerman.v Sets.vo FSignature.vo
	$(COQC) L1_Hilbert_Accerman.v

clean:
	rm -f *.vo *.vok *.vos *.glob
