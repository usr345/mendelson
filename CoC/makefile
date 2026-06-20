include ../common.mk

COQC := $(COQC) -noinit -Q . CoC

all: CoC.vo Groups.vo PeanoArithmetic.vo

CoC.vo: CoC.v
	$(COQC) CoC.v

Groups.vo: Groups.v CoC.vo
	$(COQC) Groups.v

PeanoArithmetic.vo: PeanoArithmetic.v Groups.vo CoC.vo
	$(COQC) PeanoArithmetic.v

include ../clean.mk
