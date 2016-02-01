# SimplBerry #

## Development ##

### Requirements ###
- Install OCaml.
    + Install [opam](http://opam.ocamlpro.com/), the right way to install OCaml.
    + `opam switch 4.01.0 && opam update && opam upgrade`
    + `opam install menhir ott batteries biniou cppo easy-format yojson ctypes`

- Install [Coq](http://coq.inria.fr/download) from tarball.
    + IMPORTANT: use have to configure with `./configure -usecamlp4`. The `-usecamlp4` option is required.
    + After configuration, do `make && sudo make install`

- Install [paco](plv.mpi-sws.org/paco/) library.
    + `git clone git@github.com:snu-sf/paco.git` somewhere. Command below in `/src`.
    + `make`
    + `sudo make install`

- Get [Boost](http://www.boost.org/users/history/version_1_59_0.html) C++ library.
    + Unzip somewhere.
    + Add `export BOOST_ROOT=$BOOST_LOCATION` (or `export BOOST_INCLUDEDIR=$BOOST_LOCATION`) in `.bashrc` or `.zshrc`.   

- Clone the repository.

- `git submodule init && git submodule update`
    + If above commands do not work, check format of `url` in `.gitmodules` are start with `https://github.com`.
    + If you meet `permission denied (publickey)` error when perform `git submodule update`, do `git submodule sync` && `git submodule update`

- Build `vellvm`.
    + See `https://github.com/snu-sf/vellvm-legacy` for more details.
    + `script/build-vellvm.sh $JOBS`
    + `lib/vellvm/src/` will contain `.vo` files.
    + `lib/vellvm/` will contain extracted `.ml`, `.mli` files.

- Build `llvm`.
    + `git submodule init && git submodule update` to install Cereal.
    + `script/build-llvm.sh $JOBS`
    + `.build/llvm-obj` will contain llvm object files.
    + `.local/bin` will contain llvm installation.

### Build ###
- Move `.coqrc` to `$HOME`. Here, replace $SIMPLBERRY_HOME to your simplberry directory.
- `make` in `/src`

### Debugging ###
- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### TODO ###
`src/main.ml`
- line 70: Currently we don't free memory spaces.
