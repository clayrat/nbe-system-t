# Regenerate the extracted OCaml from Coq, then build and run the demo.
#   make        - extract, build, and run
#   make extract- (re)generate nbe.ml / nbe.mli from Extract.v
#   make clean  - remove generated OCaml, the dune _build, and Coq artifacts

.PHONY: all extract run clean

all: run

nbe.ml nbe.mli: Extract.v ../theories/Model.vo
	coqc -Q ../theories NbE Extract.v

extract: nbe.ml

run: nbe.ml
	dune exec ./main.exe

clean:
	rm -f nbe.ml nbe.mli *.vo *.vok *.vos *.glob .*.aux
	rm -rf _build
