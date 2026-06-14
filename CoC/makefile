include ../common.mk

COQC := $(COQC) -noinit -Q . CoC

all: CoC.vo PeanoArithmetic.vo

CoC.vo: CoC.v
	$(COQC) CoC.v

PeanoArithmetic.vo: PeanoArithmetic.v CoC.vo
	$(COQC) PeanoArithmetic.v

include ../clean.mk
