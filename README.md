# CRELLVM #


## Structure of the Code ##

Crellvm is divided roughly into four parts: LLVM, Vellvm, proof checker, and its verification in Coq.

- LLVM is in [lib/llvm](lib/llvm/).
- Vellvm is in [lib/vellvm](lib/vellvm/).
- Proof checker is in [ocaml/](ocaml/) and [coq/def/](coq/def/).
- The verification of the proof checker in Coq is in [coq/proof/](coq/proof/).

### LLVM ###

#### Proof Generation Code in Passes ####

- For register promotion, see [PromoteMemoryToRegister.cpp](lib/llvm/lib/Transforms/Utils/PromoteMemoryToRegister.cpp).
- For GVN-PRE, see [GVN.cpp](lib/llvm/lib/Transforms/Scalar/GVN.cpp).
- For LICM, see [LICM.cpp](lib/llvm/lib/Transforms/Scalar/LICM.cpp), [LCSSA.cpp](lib/llvm/lib/Transforms/Utils/LCSSA.cpp), [SSAUpdater.cpp](lib/llvm/lib/Transforms/Utils/SSAUpdater.cpp).
- For InstCombine, see [InstCombine](lib/llvm/lib/Transforms/InstCombine) directory.

Note that, all our modifications are wrapped with `llvmberry::intrude` function.

#### Proof Generation Library ####

- [.cpp files](lib/llvm/lib/LLVMBerry)
- [.h files](lib/llvm/include/llvm/LLVMBerry)

Most of those codes are automatically-generated codes for serialization.

### Validator ###

- [def](coq/def) directory contains the definition of the proof checker and its dependency.
  + [Validator.v](coq/def/Validator.v) contains function `valid_module`, which is called from [main.ml](ocaml/main.ml).
  + [Postcond.v](coq/def/Postcond.v) contains a strong post-invariant generator.
  + [Infrules.v](coq/def/Infrules.v) contains inference rules and their semantics.
- [corehint](ocaml/corehint/) directory contains the schema for serialization.
- [main.ml](ocaml/main.ml) contains the entry point for the proof checker.  It calls `valid_module` extracted from Coq.
- [infruleGen.ml](ocaml/infruleGen.ml) contains the custom automation functions that find appropriate inference rules.

### Proof ###

- [proof](coq/proof) contains the formal verification of the proof checker in Coq.
  + [Refinement.v](coq/proof/Refinement.v) proves behavioral refinement of two modules that pass the proof checker.
  + [SimulationNop.v](coq/proof/SimulationNop.v) proves behavioral refinement for two equivalent modules modulo nops.

## Browsing the Code ##

Just after the extraction, there is no [lib/llvm](lib/llvm) directory.
Instead, there is [lib/llvm_diff_files](lib/llvm_diff_files) directory, which contains all the files that we have ever modified.
Later, below `make` commands will clone proper LLVM and copy `lib/llvm_diff_files` into `lib/llvm`.
To browse our code, you do not have to wait for `make` to be done. You can just look inside `lib/llvm_diff_files`

## Development ##

### Requirements ###

- [OCaml](http://ocaml.org/)
    + Install [opam](http://opam.ocamlpro.com/), the right way to install OCaml.
    + `opam switch 4.03.0 && opam update && opam upgrade`

- [Boost](http://www.boost.org/users/history/version_1_59_0.html)
    + `sudo yum install boost-devel`

- [CMake](https://cmake.org/) 3.3.2+
    + `sudo yum install cmake`

### Build ###
- You may want to alter "JOBS" variable inside `Makefile`, default is 24.

- `make init`
    + It installs Coq & OCaml libraries.

- `make llvm`
    + `script/llvm-build.sh`
    + `.build/llvm-obj` will contain llvm object files.
    + `opt -help` will contain some more options we added, e.g. `-llvmberry-passwhitelist=pass_name`, `-llvmberry-compactjson`

- `make exec`
    + It builds validator object file in `ocaml/main.native`
    
- `make proof`
    + It compiles proof.

### Proof Status ###

`./coq/count_admit.sh` to grep all assumption keywords (e.g. `admit`, `Axiom`) in all the Coq files.

### Testing ###

- Use `Test.scala` script, it is tested under Scala version 2.11.8.
- `scala Test.scala -h` should give some information.
- To run our Validator, you just type the following command into the command line:
    + scala `Test.scala` -j `# core` -a `option` -i `test-dir`
       * `# core` represents the number of cores to be used for testing.
       * `option` will be passed to `opt`. You can give options like “-O2”.
       * `test-dir` is the address of the benchmark you want to compile & validate.

#### Concrete Example ####

- Run `scala Test.scala -j 24 -a "-O2" -i ./sample_test`
    + This directory contains few randomly selected `.ll` files extracted from `Python 3.4.1`. For more information, please refer to [EXTRACT.md](sample_test/EXTRACT.md)
    + The output will be in `./test_result.sample_test.0`.
    + `report.summary`, `report.generate`, `report.validate` will contain test results.
