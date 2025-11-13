#
# Copyright (c) 2019-2024 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source
# License. See the LICENSE-BedRock file in the repository root for details.
#

# You can override this with a different program which you can use to preview
# html files within your filesystem.
DOCOPEN ?= xdg-open

all:
	dune build @default @runtest
.PHONY: all

_CoqProject: _CoqProject.template
	@cp $< $@

SHELL := /bin/bash

BUILD_ROOT=../../_build/default/fmdeps/BRiCk
ROCQLIB=${PWD}/../../_build/install/default/lib/coq
DOC_PATH = rocq-bluerock-brick/doc
COQDOC_DIR = $(DOC_PATH)/sphinx/_static/coqdoc

SED = $(shell which gsed 2> /dev/null || which sed 2> /dev/null)
CP = $(shell (which gcp || which cp) 2> /dev/null)

doc:
	@dune clean
	@dune build @../vendored/rocq/install
	@dune build
	@rm -rf /tmp/coqdocjs
	@cp -r coqdocjs /tmp
	@rm -rf $(DOC_PATH)/sphinx/_static/coqdoc
	@mkdir -p $(DOC_PATH)/sphinx/_static/css/coqdocjs $(DOC_PATH)/sphinx/_static/js/coqdocjs
	@$(CP) -r coqdocjs/extra/resources/*.css $(DOC_PATH)/sphinx/_static/css/coqdocjs
	@$(CP) -r coqdocjs/extra/resources/*.js $(DOC_PATH)/sphinx/_static/js/coqdocjs
	@ROCQLIB=${ROCQLIB} dune build @doc
	@rm -rf ${COQDOC_DIR}
	@mkdir -p ${COQDOC_DIR}
	@$(CP) -r -t ${COQDOC_DIR} $$(find ${BUILD_ROOT} -type d -name '*.html')
	@find ${COQDOC_DIR} -type f -name '*.html' \
		| xargs -P 16 -I {} $(SED) -i \
		-e '/{{{FOOTER}}}/{' -e 'r coqdocjs/extra/footer.html' -e 'd' -e '}' {}
	@find ${COQDOC_DIR} -type f -name '*.html' \
		| xargs -P 16 -I {} $(SED) -i \
		-e '/{{{HEADER}}}/{' -e 'r coqdocjs/extra/header.html' -e 'd' -e '}' {}
	@$(MAKE) -C $(DOC_PATH) html
.PHONY: doc

doc-open: doc
	$(DOCOPEN) $(DOC_PATH)/sphinx/_build/html/index.html
.PHONY: doc-open

doc-clean:
	@$(MAKE) -C doc clean
.PHONY: doc-clean

clean: doc-clean
	@dune clean || echo "dune not found; not cleaning dune-generated documentation files"
	@rm -f _CoqProject
.PHONY: clean
