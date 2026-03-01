include ../common.mk

COQC := $(COQC) -Q . Relevant_B -Q ../Basis Basis

all: Syntactic.vo

Formula.vo: Formula.v
	$(COQC) Formula.v

Syntactic.vo: Syntactic.v Formula.vo
	$(COQC) Syntactic.v

include ../clean.mk
