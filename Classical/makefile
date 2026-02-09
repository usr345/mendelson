include ../common.mk

COQC := $(COQC) -Q . Classical -Q ../Basis Basis

all: Meta.vo Semantic.vo Syntactic.vo

Semantic.vo: Semantic.v
	$(COQC) Semantic.v

Syntactic.vo: Syntactic.v
	$(COQC) Syntactic.v

Meta.vo: Meta.v Syntactic.vo Semantic.vo
	$(COQC) Meta.v

# L1_Hilbert_Accerman.vo: L1_Hilbert_Accerman.v Sets.vo FSignature.vo
# 	$(COQC) L1_Hilbert_Accerman.v

include ../clean.mk
