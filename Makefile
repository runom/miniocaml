#
# Makefile
#

SRC= syntax.ml parser.mly lexer.mll tinf.ml eval.ml compiler.ml main.ml 
COMPONENT= syntax.ml parser.mli parser.ml lexer.ml tinf.ml eval.ml compiler.ml main.ml 
TARGET= miniocaml

all:	$(TARGET)

$(TARGET): 	$(COMPONENT) 
	ocamlmktop $(COMPONENT) -w -31 -o $(TARGET)

parser.mli:	parser.mly
	ocamlyacc parser.mly

parser.ml:	parser.mly
	ocamlyacc parser.mly

lexer.ml:	lexer.mll
	ocamllex lexer.mll

backup:
	/bin/cp -f Makefile $(SRC) back

clean:
	/bin/rm -f parser.ml parser.mli lexer.ml $(TARGET) *.cmi *.cmo *.mli

