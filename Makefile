
.PHONY: all build watch test clean

all: build

build:
	dune build
	ln -s _build/default/bin/main.exe a.out

watch:
	dune build --watch

test: build
	@test/end2end/test.sh .

clean:
	dune clean

