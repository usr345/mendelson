include ../common.mk

COQC := $(COQC) -Q . Basis

all: EqDec.vo FSignature.vo Sets.vo MSets.vo Formula.vo

EqDec.vo: EqDec.v
	$(COQC) EqDec.v

FSignature.vo: FSignature.v
	$(COQC) FSignature.v

Sets.vo: Sets.v
	$(COQC) Sets.v

MSets.vo: MSets.v
	$(COQC) MSets.v

Formula.vo: Formula.v EqDec.vo FSignature.vo
	$(COQC) Formula.v

include ../clean.mk
