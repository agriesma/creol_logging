
creolcomp: creollex.cmo creolparser.cmo
	ocamlc $^ -o $@
	
%.cmi: %.mli
	ocamlc -c $< -o $@

%.cmo: %.ml
	ocamlc -c $< -o $@

creollex.ml: creol.mll
	ocamllex -o $@ $<

creolparser.ml creolparser.mli: creol.mly
	menhir --dump --explain --base creolparser --infer creol.mly

clean:
	rm -f creolcomp creollex.ml creolparser.ml creolparser.mli .depend

.PHONY: depend
depend: .depend

.depend:
	ocamldep creollex.ml creolparser.ml > $@

-include .depend
