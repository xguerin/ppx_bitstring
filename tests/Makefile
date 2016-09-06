default: all

clean:
	rm -f *.cm* *.o *Test *.log *.cache

build:
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -ppx ../src/ppx_bitstring.ext BitstringParserTest.ml -o BitstringParserTest
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -ppx ../src/ppx_bitstring.ext BitstringConstructorTest.ml -o BitstringConstructorTest

run:
	./BitstringParserTest
	./BitstringConstructorTest

all: clean build run
