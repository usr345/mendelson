include ../common.mk

COQC := $(COQC) -Q . Modal -Q ../Basis Basis

all: Fitting_Mendelson.vo

Fitting_Mendelson.vo:
	$(COQC) Fitting_Mendelson.v

include ../clean.mk
