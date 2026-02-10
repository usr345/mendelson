include ../common.mk

COQC := $(COQC) -Q . FDE -Q ../Basis Basis -Q ../Lattices Lattices

all: Meta.vo Exercises.vo

Formula.vo: Formula.v
	$(COQC) Formula.v

Semantics.vo: Semantics.v Formula.vo
	$(COQC) Semantics.v

Semantics_equivalence.vo: Semantics_equivalence.v Semantics.vo
	$(COQC) Semantics_equivalence.v

Exercises.vo: Exercises.v Semantics.vo
	$(COQC) Exercises.v

Syntactic.vo: Syntactic.v Formula.vo
	$(COQC) Syntactic.v

Meta.vo: Meta.v Semantics_equivalence.vo Syntactic.vo
	$(COQC) Meta.v

include ../clean.mk
