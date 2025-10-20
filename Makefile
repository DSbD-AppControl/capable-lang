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

.PHONY: ${PROJECT}-doc ${PROJECT}-srcs

$(TARGET): $(strip $(SOURCES))
	$(IDRIS2) --build ${PROJECT}.ipkg

${PROJECT}: $(TARGET)

${PROJECT}-doc:
	$(IDRIS2) --mkdoc ${PROJECT}.ipkg

${PROJECT}-srcs:
	bash annotate.sh

# -- [ Testing ]

.PHONY: ${PROJECT}-test-build ${PROJECT}-test-run ${PROJECT}-test-run-re ${PROJECT}-test-update

${PROJECT}-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

${PROJECT}-test-run: ${PROJECT}
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

${PROJECT}-test-run-re: ${PROJECT}
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

${PROJECT}-test-update: ${PROJECT}
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 THREADS=1 \
			 ONLY=$(ONLY)

# [ Benchmarks ]

.PHONY: ${PROJECT}-bench-check ${PROJECT}-bench-check-record

HYPERFINE_PARAMS := --ignore-failure --warmup 10 --sort command

${PROJECT}-bench-check: ${PROJECT}
	$(HYPERFINE) $(HYPERFINE_PARAMS) $(call fn_build_benchmarks,check,tests/classics)

${PROJECT}-bench-check-record: ${PROJECT} ${PROJECT}-test-build
	mkdir -p results/
	$(HYPERFINE) $(HYPERFINE_PARAMS) $(call fn_build_records,check) $(call fn_build_benchmarks,check,tests/classics)

${PROJECT}-bench-exec: ${PROJECT}
	$(HYPERFINE) $(HYPERFINE_PARAMS) $(call fn_build_benchmarks,run,tests/classics)

${PROJECT}-bench-exec-record: ${PROJECT} ${PROJECT}-test-build
	mkdir -p results/
	$(HYPERFINE) $(HYPERFINE_PARAMS) $(call fn_build_records,run) $(call fn_build_benchmarks,run,tests/classics)

.PHONY: plot-results

plot-results:
	make -C results results

# [ Artefact ]

.PHONY: artefact

${PROJECT}-vm:
	${MAKE} -C artefact artefact

artefact: archive ${PROJECT} ${PROJECT}-doc ${PROJECT}-srcs ${PROJECT}-vm

	mkdir -p artefact-staging

	cp ${PROJECT}.tar.gz artefact-staging/${PROJECT}.tar.gz

	tar -zcvf artefact-staging/${PROJECT}_doc.tar.gz -C ${BUILDDIR} docs

	tar -zcvf artefact-staging/${PROJECT}_html.tar.gz -C ${BUILDDIR} html

	cp artefact/output/${PROJECT}.box artefact-staging/
	cp artefact/README.md artefact-staging/

# -- [ Housekeeping ]

.PHONY: archive

archive:
	git archive \
	  --prefix=${PROJECT}/ \
	  --format=tar.gz \
	  HEAD \
	  > ${PROJECT}.tar.gz

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clobber
	find . -iname "*~" -delete
	${RM} -rf build/ artefact-staging/
	${RM} ${PROJECT}.tar.gz
	make -C results clobber

# -- [ Utilities]

# Need these for pattern substitution.
null :=
space := $(null) #

# Find all the benchmarks in a given directory.
#
# Args: directory of interest.
fn_find_bmarks = $(shell find $(1) -iname "*.capable" | sort -r )

# Generate the Hyperfine alias for the command.
#
# Args: file to be used.
#fn_gen_name = $(lastword $(subst -,$(space),$(shell dirname $(1) | xargs basename )))
fn_gen_name = $(lastword $(subst /,$(space),$(shell dirname $(1) )))

# Generate location to cd into
#
# Args: dir
fn_get_dir = $(shell dirname $(1))

fn_get_fname = $(shell basename $(1))

# Generate the command to be executed.
#
# Args: file to be used.
fn_build_cmd = -n $(call fn_gen_name,$(b)) 'cd $(call fn_get_dir,$(b)) && $(TARGET) --$(1) $(call fn_get_fname,$(b))'

# Find and generate the named commands.
#
# Args: (1) check or exec; (2) the directory to lookin
fn_build_benchmarks = $(foreach b,$(call fn_find_bmarks,$(2)),$(call fn_build_cmd,$(1)))

# Generate the locations to record timing information for each run
#
# Args: (1) check or exec;
fn_build_records = --export-csv results/$(1).csv --export-json results/$(1).json --export-markdown results/$(1).md

# -- [ EOF ]
