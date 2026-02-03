.PHONY: all clean

OUTPUT=$(shell which rocq 2>/dev/null)

ifneq ($(OUTPUT), )
    COQC=rocq c
else
    COQC=coqc
endif

COQC := $(COQC) -R . Mendelson

all: Meta.vo FDE_exercises.vo K4_exercises.vo FDE_meta.vo

FSignature.vo: FSignature.v
	$(COQC) FSignature.v

Sets.vo: Sets.v
	$(COQC) Sets.v

MSets.vo: MSets.v
	$(COQC) MSets.v

EqDec.vo: EqDec.v
	$(COQC) EqDec.v

Formula.vo: Formula.v EqDec.vo FSignature.vo
	$(COQC) Formula.v

Semantic.vo: Semantic.v Sets.vo Formula.vo
	$(COQC) Semantic.v

Syntactic.vo: Syntactic.v Sets.vo Formula.vo
	$(COQC) Syntactic.v

Meta.vo: Meta.v Syntactic.vo Semantic.vo EqDec.vo
	$(COQC) Meta.v

L1_Hilbert_Accerman.vo: L1_Hilbert_Accerman.v Sets.vo FSignature.vo
	$(COQC) L1_Hilbert_Accerman.v

# FDE

FDE_semantics.vo: FDE_semantics.v FSignature.vo Sets.vo
	$(COQC) FDE_semantics.v

FDE_semantic_equiv.vo: FDE_semantic_equiv.v FDE_semantics.vo
	$(COQC) FDE_semantic_equiv.v

FDE_exercises.vo: FDE_exercises.v FDE_semantics.vo
	$(COQC) FDE_exercises.v

FDE_syntactic.vo: FDE_syntactic.v FDE_semantics.vo FSignature.vo
	$(COQC) FDE_syntactic.v

FDE_meta.vo: FDE_meta.v FDE_semantic_equiv.vo FDE_syntactic.vo FDE_semantics.vo FSignature.vo
	$(COQC) FDE_meta.v

# K4

K4.vo: K4.v FSignature.vo MSets.vo
	$(COQC) K4.v

K4_exercises.vo: K4_exercises.v K4.vo
	$(COQC) K4_exercises.v

clean:
	rm -f *.vo *.vok *.vos *.glob
