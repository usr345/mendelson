OUTPUT=$(shell which rocq 2>/dev/null)

ifneq ($(OUTPUT), )
    COQC=rocq c
else
    COQC=coqc
endif

COQC := $(COQC) -R . Mendelson

all: Meta.vo FDE_excercises.vo K4_excercises.vo

FSignature.vo : FSignature.v
	$(COQC) FSignature.v

Sets.vo : Sets.v
	$(COQC) Sets.v

MSets.vo : MSets.v
	$(COQC) MSets.v

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

FDE.vo : FDE.v FSignature.vo Sets.vo
	$(COQC) FDE.v

FDE_excercises.vo : FDE_excercises.v FDE.vo
	$(COQC) FDE_excercises.v

FDE_syntactic.vo : FDE_syntactic.v FDE.vo FSignature.vo
	$(COQC) FDE_syntactic.v

FDE_meta.vo : FDE_meta.v FDE.vo FSignature.vo
	$(COQC) FDE_meta.v

K4.vo : K4.v FSignature.vo MSets.vo
	$(COQC) K4.v

K4_excercises.vo : K4_excercises.v K4.vo
	$(COQC) K4_excercises.v

clean:
	rm -f *.vo *.vok *.vos *.glob
