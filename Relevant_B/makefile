include ../common.mk

COQC := $(COQC) -Q . Relevant_B -Q ../Basis Basis

all: Semantic.vo Syntactic.vo Meta.vo Exercises.vo

Formula.vo: Formula.v
	$(COQC) Formula.v

Syntactic.vo: Syntactic.v Formula.vo
	$(COQC) Syntactic.v

Semantic.vo: Semantic.v Formula.vo
	$(COQC) Semantic.v

Meta.vo: Meta.v Semantic.vo Syntactic.vo
	$(COQC) Meta.v

Exercises.vo: Exercises.v Semantic.vo Syntactic.vo
	$(COQC) Exercises.v

include ../clean.mk
