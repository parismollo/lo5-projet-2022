invariants: invariants.ml
	ocamlfind ocamlopt -o invariants -linkpkg invariants.ml

clean:
	rm -f *~ *.cmi *.cmx *.o invariants
