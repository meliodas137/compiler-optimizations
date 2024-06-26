# We are not really tracking dependencies because everything is small
# enough to recompile at will.

# change to a different ocamlc if you prefer (e.g., ocamlopt)
COMPILER=ocamlc
 
all: clean cish cfg

mips:
	$(COMPILER) -c word32.ml
	$(COMPILER) -c mips.ml

cish: mips
	$(COMPILER) -c cish_ast.ml
	ocamlyacc cish_parse.mly
	$(COMPILER) -c cish_parse.mli
	$(COMPILER) -c cish_parse.ml
	ocamllex cish_lex.mll
	$(COMPILER) -c cish_lex.ml
	$(COMPILER) -c cish_eval.ml
	$(COMPILER) -c cish_compile.ml

cfg: mips cish
	$(COMPILER) -c cish_ast.ml
	$(COMPILER) -c cfg_ast.ml
	$(COMPILER) -c available.ml
	$(COMPILER) -c liveness.ml
	$(COMPILER) -c subexp_elim.ml
	$(COMPILER) -c dead_code_elem.ml
	$(COMPILER) -c conscopy_prop.ml
	$(COMPILER) -c main.ml
	$(COMPILER) -o optimize cish_ast.cmo cish_lex.cmo cish_parse.cmo word32.cmo mips.cmo cfg_ast.cmo available.cmo liveness.cmo subexp_elim.cmo dead_code_elem.cmo conscopy_prop.cmo main.cmo 

clean:
	-rm *.cmo *.cmi optimize cish_parse.ml cish_parse.mli cish_lex.ml
