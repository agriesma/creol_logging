
creolcomp: creollex.ml creolparser.ml creolparser.mli
	

creollex.ml: creol.mll
	ocamllex -o $@ $<

creolparser.ml creolparser.mli: creol.mly
	menhir --base creolparser --explain --infer creol.mly
