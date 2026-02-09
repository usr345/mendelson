include ../common.mk

COQC := $(COQC) -Q . K4_N4 -Q ../Basis Basis

all: K4_exercises.vo N4_exercises.vo

K4.vo: K4.v
	$(COQC) K4.v

K4_exercises.vo: K4_exercises.v K4.vo
	$(COQC) K4_exercises.v

N4_exercises.vo: N4_excersizes.v K4.vo
	$(COQC) N4_excersizes.v

include ../clean.mk
