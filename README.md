# ppx_bitstring

PPX plugin for the OCAML OPAM bitstring package.

## Overview

This repository is a development playground. It aims at eventually being a drop-in replacement of the `ocamlp4` extension.

## Usage

The PPX extension is called `ppx_bitstring.ext`. It should be used as follows:

```bash
$ opam pin add -k git ppx_bitstring https://github.com/xguerin/ppx_bitstring
$ ocamlfind ocamlopt -linkpkg -thread -package core,bitstring,ppx_bitstring.ext main.ml -o main.native
```

## Syntax

Usage example with the `match` PPX extension:

```ocaml
match%bitstring bs with
| {|
    1 : 1;
    a : 2;
    b : 16 : bigendian;
    ...
  |} -> (* Do something *)
| {| _ |} -> (* Do something else *)
```

Usage example with the `let` PPX extension:

```ocaml
let%bitstring bs = {|
    1 : 1;
    a : 2;
    b : 16 : bigendian;
    ...
  |} in (* Do something here *)
```

The format of the cases being the same as the original `bitstring`, please refer to its [documentation](http://people.redhat.com/~rjones/bitstring/html/Bitstring.html).

## Contribute

To see the parse tree of a ML file:

```bash
ocamlc -dparsetree foo.ml
```

To see the output of a development version of the extension:

```bash
ocamlfind opt -package bitstring,core -thread -dsource -ppx ./ppx_bitstring.ext foo.ml
```

## License

This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with this program.  If not, see <http://www.gnu.org/licenses/>.

