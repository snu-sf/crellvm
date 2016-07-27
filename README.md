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

- `make`
    + It executes `make exec` and `make proof`

- `make exec`
    + It builds `ocaml/main.native`, the validator.

- `make proof`
    + It compiles proof code, which is not yet implemented.

- `make def`, `make extract`
    + You might not need this command often.
    + `definition` only compiles Coq codes in `exec` directory, which are needed for validator execution.
    + `extract` only compiles Coq codes in `extraction` directory, which actually extracts Coq code to OCaml code that valiidator needs.

### Quick Build ###

- `make quick`, `make lib-quick`, `make def-quick`, `make extract-quick`, `make exec-quick`, `make proof-quick`
    + Same with make without `quick`, but compiles coq files with `-quick` option. It produces `*.vio` instead of `*.vo`. For more information, refer to [this](https://coq.inria.fr/refman/Reference-Manual031.html).
    + You might need to separate repository, one for `*.vo` and the other for `*.vio`. For more information, refer to [this](https://github.com/snu-sf/simplberry/pull/247).
    + Recommended way to separate repository and keep sync is using `unison`.
    + You may use original repository for `*.vio` files, only running `make` with `quick`.
    + You may add the following line in `~/.unison/default.prf`, and then execute `run_unison.sh` to keep sync.
    + You may use copied repository for `*.vo` files, only running `make` without `quick`.
        + You may not be able to run `make exec`, because it needs OCaml binding from .build directory.
        + However, `make proof` should be sufficient.
    + You may need to clear `~/.unison` correspondingly when you delete copied repository.
~~~
ignore = Name {.git,.build,simplberry-tests,*.vo,*.vio,*.zip,_CoqProject,Makefile.coq}
~~~

### Debugging ###

- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### TODO ###

- `before_refact` branch represents the branch before refactoring, containing old proof codes.
- `src/main.ml:70`: Currently we don't free memory spaces.
