# -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

PROJECT=capable
IDRIS2=idris2

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${PROJECT}

# [ Core Project Definition ]

.PHONY: capable capable-test-build capable-test-run capable-test-run-re capable-test-update \
       # capable-bench

capable:
	$(IDRIS2) --build ${PROJECT}.ipkg

# To be activated once frontend is completed.

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


# [ Housekeeping ]

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/

# -- [ EOF ]
