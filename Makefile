all: lib 

lib:
	make -C src

tests:

clean:
	make -C src clean
	make -C tests clean

install:
	make -C src install
