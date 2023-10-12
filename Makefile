 # -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

PROJECT=capable
IDRIS2=idris2
KATLA=katla
HYPERFINE=hyperfine

BUILDDIR  = ${CURDIR}/build
TARGETDIR = ${BUILDDIR}/exec
TARGET    = ${TARGETDIR}/${PROJECT}

BENCHMARKS= --parameter-list benchmark 000,001,002
RESULTS= --export-json results.json --export-markdown results.md

# [ Core Project Definition ]

.PHONY: capable capable-doc capable-srcs
.PHONY: capable-test-build capable-test-run capable-test-run-re capable-test-update
.PHONY: capable-bench capable-bench-check

capable:
	$(IDRIS2) --build ${PROJECT}.ipkg

capable-doc:
	$(IDRIS2) --mkdoc ${PROJECT}.ipkg

capable-srcs:
	bash annotate.sh

capable-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

capable-test-run: capable-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

capable-test-run-re: capable-test-build
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

capable-test-update: capable-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 THREADS=1 \
			 ONLY=$(ONLY)

capable-bench: capable capable-test-build
	$(HYPERFINE) $(BENCHMARKS) '${MAKE} -C tests benchmark IDRIS2=$(IDRIS2) PROG_BIN=$(TARGET) ONLY={benchmark}'

capable-bench-record: capable capable-test-build
	$(HYPERFINE) $(BENCHMARKS) $(RESULTS) '${MAKE} -C tests benchmark IDRIS2=$(IDRIS2) PROG_BIN=$(TARGET) ONLY={benchmark}'


#	$(HYPERFINE) --warmup 10 '${MAKE} capable-test-run'

# [ Artefact ]

.PHONY: artefact

capable-vm:
	${MAKE} -C artefact artefact

artefact: archive capable capable-doc capable-srcs capable-vm

	mkdir -p artefact-staging

	cp capable.tar.gz artefact-staging/capable.tar.gz

	tar -zcvf artefact-staging/capable_doc.tar.gz -C ${BUILDDIR} docs

	tar -zcvf artefact-staging/capable_html.tar.gz -C ${BUILDDIR} html

	cp artefact/output/capable.box artefact-staging/
	cp artefact/README.md artefact-staging/

# [ Housekeeping ]

.PHONY: archive

archive:
	git archive \
	  --prefix=capable/ \
	  --format=tar.gz \
	  HEAD \
	  > capable.tar.gz

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/
	${RM} -rf artefact-staging/
	${RM} capable.tar.gz
	${RM} results.json results.md

# -- [ EOF ]
