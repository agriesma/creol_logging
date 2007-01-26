src	= creol.mli creol.ml Creol.mll Creol.mly Driver.ml
parser	= CreolLex.ml CreolParser.ml CreolParser.mli

creolcomp: CreolLex.cmo CreolParser.cmo creol.cmo Driver.cmo
	ocamlc $^ -o $@

%.cmi: %.mli
	ocamlc -c $< -o $@

%.cmo: %.ml
	ocamlc -c $< -o $@

CreolLex.ml: Creol.mll
	ocamllex -o $@ $<

CreolParser.ml CreolParser.mli: Creol.mly creol.cmi
	menhir --dump --explain --base CreolParser --infer $<

clean:
	rm -f creolcomp
	rm -f CreolLex.ml CreolParser.ml CreolParser.mli
	rm -f *.cmo *.cmi

.PHONY: depend
depend: .depend

.depend: $(src) $(parser)
	ocamldep $^ > $@

-include .depend
