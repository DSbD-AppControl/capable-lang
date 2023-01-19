# -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

PROJECT=capable
IDRIS2=idris2
KATLA=katla

BUILDDIR  = ${CURDIR}/build
TARGETDIR = ${BUILDDIR}/exec
TARGET    = ${TARGETDIR}/${PROJECT}

# [ Core Project Definition ]

.PHONY: capable capable-doc capable-srcs
.PHONY: capable-test-build capable-test-run capable-test-run-re capable-test-update
#.PHONY: capable-bench

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
	${ECHO} "Todo"

#	$(HYPERFINE) --warmup 10 '${MAKE} capable-test-run'

# [ Artefact ]

.PHONY: artefact

capable-vm:
	${MAKE} -C artefact artefact

artefact: archive capable capable-doc capable-srcs capable-vm
	mkdir -p artefact-staging
	cp capable.tar.gz artefact-staging/capable.tar.gz
	tar -zcvf artefact-staging/capable_doc.tar.gz ${BUILDDIR}/docs/
	tar -zcvf artefact-staging/capable_html.tar.gz ${BUILDDIR}/html/
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

# -- [ EOF ]
