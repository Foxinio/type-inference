
.PHONY: all build watch test tex clean clean-all

all: build tex

build:
	dune build

watch:
	dune build --watch

test: build
	@test/end2end/test.sh .

tex:
	$(MAKE) -C tex paper.pdf
	$(MAKE) -C tex notes.pdf
	$(MAKE) -C tex przyklad.pdf

clean:
	dune clean
	$(MAKE) -C tex clean

clean-all:
	dune clean
	latexmk -C tex clean-all
