# Development #

## Requirements ##
- Install OCaml.
    + Install [opam](http://opam.ocamlpro.com/), the right way to install OCaml.
    + `opam switch 4.01.0 && opam update && opam upgrade`
    + `opam install menhir ott batteries biniou cppo easy-format yojson`

- Install [Coq](http://coq.inria.fr/download) from tarball.
    + IMPORTANT: use have to configure with `./configure -usecamlp4`. The `-usecamlp4` option is required.
    + After configuration, do `make && sudo make install`

- Install [paco](plv.mpi-sws.org/paco/) library.
    + `git clone git@github.com:snu-sf/paco.git` somewhere. Command below in `/src`.
    + `make`
    + `sudo make install`

- Clone the repository.

- `git submodule init && git submodule update`

- Build `vellvm`.
    + See `https://github.com/snu-sf/vellvm-legacy` for more details.
    + `script/build-vellvm.sh $JOBS`
    + `lib/vellvm/src/` will contain `.vo` files.
    + `lib/vellvm/` will contain extracted `.ml`, `.mli` files.

- Build `llvm`.
    + `script/build-llvm.sh $JOBS`
    + `.build/llvm-obj` will contain llvm object files.
    + `.local/bin` will contain llvm installation.

## Build ##
- Move `.coqrc` to `$HOME`. Here, replace $SIMPLBERRY_HOME to your simplberry directory.
- `make` in `/src`
