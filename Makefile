COQC := coqc
OCAMLFIND := ocamlfind
OCAMLOPT := ocamlopt

.PHONY: all coq ocaml test clean

all: coq ocaml

coq: eurocode8.vo

eurocode8.vo: eurocode8.v
	$(COQC) -Q . Eurocode8 $<

ocaml: eurocode8.ml test_eurocode8.ml
	$(OCAMLOPT) -o test_eurocode8 eurocode8.ml test_eurocode8.ml

test: ocaml
	./test_eurocode8

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux eurocode8.ml
	rm -f *.cmi *.cmo *.cmx *.o test_eurocode8 test_eurocode8.exe
