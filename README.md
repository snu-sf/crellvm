# SimplBerry #

## Development ##

### Requirements ###

- [OCaml](http://ocaml.org/)
    + Install [opam](http://opam.ocamlpro.com/), the right way to install OCaml.
    + `opam switch 4.02.3 && opam update && opam upgrade`

- [Boost](http://www.boost.org/users/history/version_1_59_0.html)
    + `sudo yum install boost-devel`

- [CMake](https://cmake.org/) 3.3.2+
    + `sudo yum install cmake`

### Build ###

- `make init`
    + It installs Coq & OCaml libraries.
    + It (recursively) downloads submodules.
    + If above commands do not work, check format of `url` in `.gitmodules` starts with `git@github.com:snu-sf/`.
    + If you meet `permission denied (publickey)` error when perform `git submodule update`, do `git submodule sync` && `git submodule update`

- `make lib`
    + It builds `vellvm-legacy`.  See `https://github.com/snu-sf/vellvm-legacy` for more details.
    + `lib/vellvm/src/` will contain `.vo` files.
    + `lib/vellvm/src/Extraction` will contain extracted `.ml`, `.mli` files.

- `make llvm`
    + `script/llvm-build.sh`
    + `.build/llvm-obj` will contain llvm object files.
    + `build/bin` will contain llvm installation.

- `make exec`

- `make proof`

### Debugging ###

- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### TODO ###

- `src/main.ml:70`: Currently we don't free memory spaces.
