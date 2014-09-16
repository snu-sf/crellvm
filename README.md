# Development #

## Requirements ##
* Install [opam](http://opam.ocamlpro.com/), the right way to install OCaml.
* `opam switch 4.01.0 && opam update && opam upgrade`
* `opam install menhir ott yojson`
* Install [Coq](http://coq.inria.fr/download) from tarball. IMPORTANT: use have to configure with `./configure -usecamlp4`. The `-usecamlp4` option is required. After configuration, do `make && sudo make install`
* Clone the repository.
* `git submodule init && git submodule update`

## Build ##
* 
