COMPILER = ocamlfind ocamlopt
FLAGS    = -package compiler-libs.common,bitstring,core,ppx_tools.metaquot,ppx_driver,ppx_core -linkpkg -thread
SOURCES	 = ppx_bitstring.ml
TARGET	 = ppx_bitstring.ext

all:
	$(COMPILER) $(FLAGS) -predicates ppx_driver $(SOURCES) ppx_driver_runner.cmxa -o $(TARGET)

install: all
	mkdir -p $(PREFIX)/lib/ppx_bitstring
	cp $(TARGET) META $(PREFIX)/lib/ppx_bitstring/

clean:
	rm -f *.cm* *.o $(TARGET)
