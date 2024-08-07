# Argument folding analysis prototype

## Language
This program takes in code in ML-like language (refer to tests for syntax).
Some fundamental features are implemented:
- ML let-polymorphism,
- Recursive algebraic data types,
- Basic builtin types and functions.

## Objective
All this to showcase argument folding analysis that is performed on the next stage.
Objective of this analysis is to minimize number of cloasure alocations,
by allowing multi-argument functions to be part of the type system.

For exact theory behind it wait for paper that is currently in the making.

## Usage
### Requirements
- `dune 3.13`
- `ocaml 4.10.0`
- `ocamllex` and `ocamlyacc`

### Build
Project can be build using `dune build` or `make build`.

### Run
Using `make build` will create `a.out` link in main directory.
To run only file with code is required.

Useful cmd flags are:
```
--use-analysis   - will force program to use mentioned analysis.
                   (this is also done by default)

--crude-analysis - will disable analysis and force program to be executed
                   as if all functions took only one argument (and were impure).

--print-states
--no-print-stats - will enable and disable printing of allocation counter
                   (this is enabled by default).
```
Other flags are used for mostly for debugging.

