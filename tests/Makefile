default: all

clean:
	rm -f *.cm* *.o *Test *.log *.cache *.source

build:
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -ppx ../src/ppx_bitstring.ext BitstringParserTest.ml -o BitstringParserTest
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -ppx ../src/ppx_bitstring.ext BitstringConstructorTest.ml -o BitstringConstructorTest
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -ppx ../src/ppx_bitstring.ext BitstringQualifierTest.ml -o BitstringQualifierTest

source:
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -dsource -ppx ../src/ppx_bitstring.ext BitstringParserTest.ml > BitstringParserTest.source 2>&1
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -dsource -ppx ../src/ppx_bitstring.ext BitstringConstructorTest.ml > BitstringConstructorTest.source 2>&1
	ocamlfind opt -package bitstring,oUnit,core -thread -linkpkg -dsource -ppx ../src/ppx_bitstring.ext BitstringQualifierTest.ml > BitstringQualifierTest.source 2>&1

run:
	./BitstringParserTest
	./BitstringConstructorTest
	./BitstringQualifierTest

all: clean build run
