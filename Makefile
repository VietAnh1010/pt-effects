build: Makefile.rocq
	$(MAKE) -f Makefile.rocq
.PHONY: build

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
.PHONY: clean

cleanall: Makefile.rocq
	$(MAKE) -f Makefile.rocq cleanall
	rm Makefile.rocq Makefile.rocq.conf
.PHONY: cleanall

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o $@
