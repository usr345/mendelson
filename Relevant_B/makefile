include ../common.mk

COQC := $(COQC) -Q . Relevant_B -Q ../Basis Basis

all: Semantic.vo Syntactic.vo

Formula.vo: Formula.v
	$(COQC) Formula.v

Syntactic.vo: Syntactic.v Formula.vo
	$(COQC) Syntactic.v

Semantic.vo: Semantic.v Formula.vo
	$(COQC) Semantic.v

include ../clean.mk
