EXTRA_DIR:=extra
ROCQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export ROCQDOCFLAGS

.PHONY: all rocq clean html
all: rocq

%: Makefile.rocq phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f Makefile.rocq $@
phony: ;


rocq: Makefile.rocq
	$(MAKE) -f Makefile.rocq
# rocq:
# 	dune build

html: Makefile.rocq
	rm -rf html
	$(MAKE) -f Makefile.rocq html
	cp $(EXTRA_DIR)/resources/* html

Makefile.rocq:
	rocq makefile -f _RocqProject -o Makefile.rocq

Makefile.rocq.conf:
	rocq makefile -f _RocqProject -o Makefile.rocq

include Makefile.rocq.conf

skip-qed: Makefile.rocq.conf
	./disable-qed.sh $(ROCQMF_VFILES)

ci: skip-qed
	$(MAKE) -f Makefile.rocq pretty-timed

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
	rm -f Makefile.rocq
	rm -rf html
