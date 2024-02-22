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

SOURCES = $(shell find src -iname "*.idr")

# [ Core Project Definition ]

.PHONY: capable-doc capable-srcs

$(TARGET): $(strip $(SOURCES))
	$(IDRIS2) --build ${PROJECT}.ipkg

capable: $(TARGET)

capable-doc:
	$(IDRIS2) --mkdoc ${PROJECT}.ipkg

capable-srcs:
	bash annotate.sh

# -- [ Testing ]

.PHONY: capable-test-build capable-test-run capable-test-run-re capable-test-update

capable-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

capable-test-run: capable
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

capable-test-run-re: capable
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

capable-test-update: capable
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 THREADS=1 \
			 ONLY=$(ONLY)

# [ Benchmarks ]

.PHONY: capable-bench-check capable-bench-check-record

HYPERFINE_PARAMS := --ignore-failure --warmup 10

capable-bench-check: capable
	$(HYPERFINE) $(HYPERFINE_PARAMS) $(call fn_build_benchmarks,check,tests/classics)

capable-bench-check-record: capable capable-test-build
	mkdir -p results/
	$(HYPERFINE) $(HYPERFINE_PARAMS) $(call fn_build_records,check) $(call fn_build_benchmarks,check,tests/classics)

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

# -- [ Housekeeping ]

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
	find . -iname "*~" -delete
	${RM} -rf build/ artefact-staging/ results/
	${RM} capable.tar.gz


# -- [ Utilities]

# Need these for pattern substitution.
null :=
space := $(null) #

# Find all the benchmarks in a given directory.
#
# Args: directory of interest.
fn_find_bmarks = $(shell find $(1) -iname "*.capable" )

# Generate the Hyperfine alias for the command.
#
# Args: file to be used.
fn_gen_name = $(lastword $(subst -,$(space),$(shell dirname $(1) | xargs basename )))

# Generate the command to be executed.
#
# Args: file to be used.
fn_build_cmd = -n $(call fn_gen_name,$(b)) '$(TARGET) --$(1) $(b)'

# Find and generate the named commands.
#
# Args: (1) check or exec; (2) the directory to lookin
fn_build_benchmarks = $(foreach b,$(call fn_find_bmarks,$(2)),$(call fn_build_cmd,$(1)))

# Generate the locations to record timing information for each run
#
# Args: (1) check or exec;
fn_build_records = --export-csv results/$(1).csv --export-json results/$(1).json --export-markdown results/$(1).md

# -- [ EOF ]
