.PHONY: all clean

OUTPUT=$(shell which rocq 2>/dev/null)

ifneq ($(OUTPUT), )
    COQC=rocq c
else
    COQC=coqc
endif