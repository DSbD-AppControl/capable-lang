# -- [ Makefile ]
#
# Makefile for the project's test suite.
#
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see ../LICENSE
#
# -- [ EOH ]

PROJECT=testing
IDRIS2=idris2
HYPERFINE=hyperfine


TARGETDIR = ./build/exec
TARGET = ${TARGETDIR}/capable-tests

UPDATE ?= --interactive
THREADS ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

# [ Testing Targets ]

$(TARGET): Main.idr
	${IDRIS2} --build ${PROJECT}.ipkg

.PHONY: testbin test test-re

# Build the test suite
testbin: $(TARGET)


# Run the test suite storing failures in the failure file.
test: testbin
	${TARGET}               \
	$(PROG_BIN)             \
	--timing                \
	$(UPDATE)               \
	--threads $(THREADS)    \
	--failure-file failures \
	--only $(ONLY)

# Only re-run the failed tests.
test-re: testbin
	${TARGET}           \
	$(PROG_BIN)          \
	$(UPDATE)             \
	--timing               \
	--failure-file failures \
	--threads $(THREADS)     \
	--only-file failures      \
	--only $(ONLY)

# [ Housekeeping ]

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	@find . -type f -name 'output' | xargs rm -f

clobber: clean
	${RM} -rf build/
	${RM} -rf failures

# -- [ EOF ]
