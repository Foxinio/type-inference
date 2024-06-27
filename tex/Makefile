NAME = paper
.PHONY: $(NAME).pdf clean clean-all

%.pdf: %.tex
		latexmk -pdf -use-make -f $<

clean:
		latexmk -c

clean-all:
		latexmk -C
