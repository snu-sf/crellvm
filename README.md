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
    + It (recursively) clones repositories including llvm, vellvm to lib/ dir, and also clones simplberry-tests repository.
    + If above commands do not work, check format of `url` in `.gitmodules` starts with `git@github.com:snu-sf/`.
    + It also buildss & installs llvm.
    + `.build/llvm-obj` will contain llvm object files.
    + `install/bin` will contain llvm installation.
    + You may want to alter "JOBS" variable, default is 8.

- `make lib`
    + It builds `vellvm-legacy`.  See `https://github.com/snu-sf/vellvm-legacy` for more details.
    + `lib/vellvm/src/` will contain `.vo` files.
    + `lib/vellvm/src/Extraction` will contain extracted `.ml`, `.mli` files.
    + It also builds sflib and paco.

- `make llvm`
    + You may want to alter "JOBS" variable, default is 24.
    + `script/llvm-build.sh`
    + `.build/llvm-obj` will contain llvm object files.

- `make opt`
    + It *only* builds "opt" executable in `.build/llvm-obj/bin`.

- `make exec`
    + It builds `ocaml/main.native`, the validator.

- `make proof`
    + It compiles proof code, which is not yet implemented.

### Debugging ###

- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### TODO ###

- `before_refact` branch represents the branch before refactoring, containing old proof codes.
- `src/main.ml:70`: Currently we don't free memory spaces.
