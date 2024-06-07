
.PHONY: all build watch test tex clean clean-all

all: build tex

build:
	dune build

watch:
	dune build --watch

test: build
	@test/end2end/test.sh .

tex:
	latexmk -C tex

clean:
	latexmk -c
	dune clean
	rm -f paper.pdf
	latexmk -C tex clean

clean-all:
	latexmk -C
	latexmk -C tex clean-all
