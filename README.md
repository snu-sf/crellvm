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
- You may want to alter "JOBS" variable, default is 24.

- `make init`
    + It installs Coq & OCaml libraries.
    + It (recursively) clones repositories including llvm, vellvm to lib/ dir, and also clones simplberry-tests repository.
    + If above commands do not work, check format of `url` in `.gitmodules` starts with `git@github.com:snu-sf/`.
    + It also buildss & installs llvm.
    + `.build/llvm-obj` will contain llvm object files.
    + `install/bin` will contain llvm installation.

- `make llvm`
    + `script/llvm-build.sh`
    + `.build/llvm-obj` will contain llvm object files.

- `make opt`
    + It *only* builds "opt" executable in `.build/llvm-obj/bin`.

### Quick Build ###

+ Compiles coq files with `-quick` option. It produces `*.vio` instead of `*.vo`. For more information, refer to [this](https://coq.inria.fr/refman/Reference-Manual031.html).
+ It needs separate copy of whole repository, so one is for `*.vo` and the other is for `*.vio`. For more information, refer to [this](https://github.com/snu-sf/simplberry/pull/247). What you need to know is do *NOT* compile with/without quick option inside same directory.
+ There is *NO* `make extract-quick`, as `-quick` option ignores extraction. Therefore, there is no `make exec-quick` neither. For more information, refer to [this](https://github.com/snu-sf/simplberry/issues/236#issuecomment-235553528).

- `make proof-quick`
    + It compiles proof code with `-quick` option.
    + Compiling proof code requires compiling all other coq codes, so it also do that.

#### Rsync ####

- Currently, the Makefile supports one possible workflow.

- `make exec-rsync`
    + Create `.proof_build` directory, copying *minimal complete* files needed for coq compile in this directory recursively.
    + Extract `*.ml`, `*.mli` files inside `.proof_build` by compiling coq code without `-quick` option.
    + Pull extracted `*.ml`, `*.mli` files back to current directory.
    + This is done with `rsync`.

- `make proof-with-rysnc`
    + Similar to `make exec-rsync`, it executes same rsync scripts to copy current coq files into `.proof_build` directory.
    + Compile proof code without `-quick` option inside `.proof_build`.

- The desire behind this design decision is: User may only want to read/update codes inside current directory, and do not care `.proof_build` directory at all.

### Debugging ###

- For those who participate in this project, there are some useful techniques to track a program flow of validator or identify cause of a bug.
    + `export OCAMLRUNPARAM='b'` lets validator show call stack when it aborts

### Related Projects ###

- [atdtocpp](https://github.com/aqjune/atdtocpp) automatically converts `.atd` file to `.cpp`/`.h` file. This may not be suitable for whole file conversion, but it may be sufficient to support simple inference rule conversions. You may need to convert the whole `.atd` file, and then just excerpt wanted part from it.
- [parallel testing](https://github.com/alxest/simplberry-tests-parallel) You may just copy `src/main/scala/main.scala` and use it. `scala main.scala -h` should give sufficient information. You may need to run with `-J-Xmx64g` or something, to manually set JVM memory limit. Required scala version or more detailed information will be in that repository.

### TODO ###

- `before_refact` branch represents the branch before refactoring, containing old proof codes.
- `src/main.ml:70`: Currently we don't free memory spaces.
