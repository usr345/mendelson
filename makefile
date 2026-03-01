.PHONY: all clean lattices basis classical fde k4 modal

COQDEP = coqdep

all: lattices basis classical fde k4 modal

# 1. Build Lattices
lattices:
	$(MAKE) -C Lattices

# 2. Build Basis
basis:
	$(MAKE) -C Basis

# 3. Build Classical
classical: basis
	$(MAKE) -C Classical

# 4. Build FDE
fde: basis lattices
	$(MAKE) -C FDE

# 5. Build Relevant_B
relevent_b: basis
	$(MAKE) -C Relevant_B

# 6. Build K4_N4
k4: basis
	$(MAKE) -C K4_N4

# 7. Build Modal
modal: basis
	$(MAKE) -C Modal

clean:
	$(MAKE) -C Lattices clean || true
	$(MAKE) -C Basis clean || true
	$(MAKE) -C Classical clean || true
	$(MAKE) -C FDE clean || true
	$(MAKE) -C Relevant_B clean || true
	$(MAKE) -C K4_N4 clean || true
	$(MAKE) -C Modal clean || true
