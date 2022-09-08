# -- [ Makefile ]
#
# Makefile for the project.
#
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
#
# -- [ EOH ]

PROJECT=ola
IDRIS2=idris2

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${PROJECT}

# [ Core Project Definition ]

.PHONY: ola # ola-test-build ola-test-run ola-test-run-re ola-test-update ola-bench

ola:
	$(IDRIS2) --build ${PROJECT}.ipkg

# To be activated once frontend is completed.

ola-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

ola-test-run: ola-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

ola-test-run-re: ola-test-build
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

ola-test-update: ola-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

ola-bench: ola ola-test-build
	${ECHO} "Todo"

#	$(HYPERFINE) --warmup 10 '${MAKE} ola-test-run'


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
