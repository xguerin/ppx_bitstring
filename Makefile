all: clean build test

clean:
	jbuilder clean

build:
	jbuilder build

test:
	jbuilder runtest

