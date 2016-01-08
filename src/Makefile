COMPILER = ocamlfind ocamlopt
FLAGS		 = -package compiler-libs.common,bitstring,core,ppx_tools.metaquot -linkpkg -thread 
SOURCES	 = ppx_bitstring.ml
TARGET	 = ppx_bitstring.ext

all:
	$(COMPILER) $(FLAGS) -o $(TARGET) $(SOURCES)

install: all
	mkdir -p $(PREFIX)/lib/ppx_bitstring
	cp $(TARGET) META $(PREFIX)/lib/ppx_bitstring/

clean:
	rm -f *.cm* *.o $(TARGET)
