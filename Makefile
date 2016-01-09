all: lib 

lib:
	make -C src
	make -C tests

tests:

clean:
	make -C src clean
	make -C tests clean

install:
	make -C src install
