# SimplBerry #

## Development ##

### Requirements ###

- Install OCaml, Coq & Libraries.
    + Install [opam](http://opam.ocamlpro.com/), the right way to install OCaml.
    + `opam switch 4.02.3 && opam update && opam upgrade`
    + `opam install menhir ott batteries biniou cppo easy-format yojson atdgen ctypes coq.8.5.0~camlp4`

- Get [Boost](http://www.boost.org/users/history/version_1_59_0.html) C++ library.
    + Unzip somewhere.
    + Add `export BOOST_ROOT=$BOOST_LOCATION` (or `export BOOST_INCLUDEDIR=$BOOST_LOCATION`) in `.bashrc` or `.zshrc`.   

### Build ###

- `make init`
    + It (recursively) downloads submodules.
    + If above commands do not work, check format of `url` in `.gitmodules` starts with `git@github.com:snu-sf/`.
    + If you meet `permission denied (publickey)` error when perform `git submodule update`, do `git submodule sync` && `git submodule update`

- `make lib`
    + It builds `vellvm-legacy`.  See `https://github.com/snu-sf/vellvm-legacy` for more details.
    + `lib/vellvm/src/` will contain `.vo` files.
    + `lib/vellvm/src/Extraction` will contain extracted `.ml`, `.mli` files.

- Build `llvm`.
    + `script/build-llvm.sh $JOBS`
    + `.build/llvm-obj` will contain llvm object files.
    + `.local/bin` will contain llvm installation.

- `make exec`

- `make proof`

### Debugging ###

- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### TODO ###

- `src/main.ml:70`: Currently we don't free memory spaces.
