src = creol.mli creol.ml creol.mll creol.mly
parser = creollex.ml creolparser.ml creolparser.mli

creolcomp: creollex.cmo creolparser.cmo creol.cmo
	ocamlc $^ -o $@

%.cmi: %.mli
	ocamlc -c $< -o $@

%.cmo: %.ml
	ocamlc -c $< -o $@

creollex.ml: creol.mll
	ocamllex -o $@ $<

creolparser.ml creolparser.mli: creol.mly creol.cmi
	menhir --dump --explain --base creolparser --infer creol.mly

clean:
	rm -f creolcomp creollex.ml creolparser.ml creolparser.mli .depend

.PHONY: depend
depend: .depend

.depend: $(src) $(parser)
	ocamldep $^ > $@

-include .depend
