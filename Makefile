.PHONY: all clean

all:
	$(MAKE) -C FixTypeSafety/
	$(MAKE) -C BasicImpExample/
	$(MAKE) -C FibExample/
	$(MAKE) -C CanonNatExample/

clean:
	$(MAKE) -C FixTypeSafety/ clean
	$(MAKE) -C BasicImpExample/ clean
	$(MAKE) -C FibExample/ clean
	$(MAKE) -C CanonNatExample/ clean
	$(MAKE) -C CanonNatExample/ cleanall

