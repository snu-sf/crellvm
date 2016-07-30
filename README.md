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
    + You may want to alter "JOBS" variable, default is 24.

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

- `make quick`, `make lib-quick`, `make def-quick`, `make proof-quick`
    + Same with make without `quick`, but compiles coq files with `-quick` option. It produces `*.vio` instead of `*.vo`. For more information, refer to [this](https://coq.inria.fr/refman/Reference-Manual031.html).
    + It needs separate copy of whole repository, so one is for `*.vo` and the other is for `*.vio`. For more information, refer to [this](https://github.com/snu-sf/simplberry/pull/247). What you need to know is do *NOT* compile with/without quick option inside same directory.

- `make extract-quick`, `make exec-quick`,
    + There is *NO* `make extract-quick`, as `-quick` option ignores extraction. Therefore, there is no `make exec-quick` neither. For more information, refer to [this](https://github.com/snu-sf/simplberry/issues/236#issuecomment-235553528).

#### Rsync ####

- Currently, the Makefile supports one possible workflow.

- `make exec-with-rsync`
    + This creates `.proof_build` directory, copying *minimal complete* files needed for coq compile in this directory recursively. It do `make extract` inside `.proof_build`, and pull extracted `*.ml`, `*.mli` files back to current directory. This is done with `rsync`.

- `make proof-with-rysnc`
    + Similar to `make exec-with-rsync`, it executes same rsync scripts to copy *minimal complete* files needed for coq compile in this directory, and then execute `make proof` inside `.proof_build`.

- The desire behind this design decision is: User may only want to read/update codes inside current directory, and do not care `.proof_build` directory at all.

### Debugging ###

- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### TODO ###

- `before_refact` branch represents the branch before refactoring, containing old proof codes.
- `src/main.ml:70`: Currently we don't free memory spaces.
