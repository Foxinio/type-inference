
.PHONY: all build watch test tex clean clean-all

all: build tex

build:
	dune build

watch:
	dune build --watch

test: build
	dune runtest

tex:
	$(MAKE) -C tex

clean:
		latexmk -c
		dune clean
		rm -f paper.pdf
		$(MAKE) -C tex clean

clean-all:
		latexmk -C
		$(MAKE) -C tex clean-all
