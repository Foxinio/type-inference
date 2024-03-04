
NAME = type-systems
.PHONY: $(NAME).pdf clean clean-all

build:
	dune build

watch:
	dune build --watch

test: build
	dune runtest

$(NAME).pdf: $(NAME).tex
		latexmk -pdf -use-make $<

clean:
		latexmk -c
		dune clean

clean-all:
		latexmk -C
