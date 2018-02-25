# Crellvm: Verified Credible Compilation for LLVM


## Code Structure

Crellvm is divided roughly into the following four parts:

- LLVM in `lib/llvm` (https://github.com/snu-sf/crellvm-llvm)
- Vellvm in `lib/vellvm` (https://github.com/snu-sf/vellvm-legacy)
- ERHL proof checker in [ocaml/](ocaml/) and [coq/def/](coq/def/)
- Formal verification of the ERHL proof checker in [coq/proof/](coq/proof/)


### LLVM

#### Proof Generation Code in Each Pass

- Register promotion: [PromoteMemoryToRegister.cpp](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Transforms/Utils/PromoteMemoryToRegister.cpp)
- GVN-PRE: [GVN.cpp](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Transforms/Scalar/GVN.cpp)
- LICM: [LICM.cpp](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Transforms/Scalar/LICM.cpp), [LCSSA.cpp](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Transforms/Utils/LCSSA.cpp), [SSAUpdater.cpp](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Transforms/Utils/SSAUpdater.cpp)
- InstCombine: files in the [InstCombine](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Transforms/InstCombine) directory

Note that all our modifications are wrapped in the `crellvm::intrude()` function.

#### Proof Generation Library

- [.cpp files](https://github.com/snu-sf/crellvm-llvm/blob/master/lib/Crellvm)
- [.h files](https://github.com/snu-sf/crellvm-llvm/blob/master/include/llvm/Crellvm)

Most of those codes are automatically-generated codes for serialization.


### Validator

- [def](coq/def) contains the definition of the proof checker and its dependency.
    + [Validator.v](coq/def/Validator.v) contains function `valid_module`, which is called from [main.ml](ocaml/main.ml).
    + [Postcond.v](coq/def/Postcond.v) contains a strong post-invariant generator.
    + [Infrules.v](coq/def/Infrules.v) contains inference rules and their semantics.
- [corehint](ocaml/corehint/) contains the schema for serialization.
- [main.ml](ocaml/main.ml) contains the entry point for the proof checker.  It calls `valid_module` extracted from Coq.
- [infruleGen.ml](ocaml/infruleGen.ml) contains the custom automation functions that find appropriate inference rules.


### Proof

- [proof](coq/proof) contains the formal verification of the proof checker in Coq.
  + [Refinement.v](coq/proof/Refinement.v) proves behavioral refinement of two modules that pass the proof checker.
  + [SimulationNop.v](coq/proof/SimulationNop.v) proves behavioral refinement for two equivalent modules modulo nops.



## Development

### Requirements

- Git
    + In Ubuntu 16.04, `sudo apt install git`

- A C++ compiler, [Boost](http://www.boost.org/users/history/version_1_59_0.html), and [CMake](https://cmake.org/) 3.3.2+
    + In Ubuntu 16.04, `sudo apt install gcc libboost-all-dev cmake`

- [OPAM](http://opam.ocamlpro.com/): the OCaml package manager
    + In Ubuntu 16.04, `sudo apt install opam m4 pkg-config`
    + Also execute `opam init && opam update && opam switch 4.05.0`

- [Scala](https://www.scala-lang.org/) 2.11.6+ for `make test`
    + In Ubuntu 16.04, `sudo apt install scala`


### Build

You can build the proof-generating LLVM compiler and the ERHL proof checker as follows.  (You can
change the `JOBS` variable, whose default is 24.  For example, you may want to `make JOBS=8 llvm`
for systems with 8 CPUs.)

- `make init`: Installs Coq and OCaml libraries, and fetches and builds dependencies.

- `make update`: Updates dependencies.

- `make all` (default): `make llvm exec proof`

- `make quick`: `make llvm exec proof-quick`

- `make llvm`: Builds LLVM in `.build/llvm-obj`.

- `make opt`: Builds proof-generating LLVM IR optimizer in `.build/llvm-obj/bin/opt`.

- `make exec`: Builds the ERHL proof checker in `ocaml/main.native`.

- `make proof`: Compiles the Coq verification of the ERHL proof checker.

- `make proof-quick`: Compiles the Coq verification with the `-quick` option (useful for interactive
  theorem proving).


### Execution

The following executables are generated in the build process:

- `.build/llvm-obj/bin/opt`: an LLVM IR optimizer, but it also generates ERHL proofs

  See `opt -help` for the additional options for proof generation,
  e.g. `-crellvm-passwhitelist=pass_name`, `-crellvm-compactjson`.

- `ocaml/main.native`: the ERHL proof checker

  `ocaml/main.native $SRC $TGT $PROOF` validates a translation from `$SRC` to `$TGT` using `$PROOF`
  as the ERHL translation proof. See `ocaml/main.native -help` for more details.

- FIXME: example!

  ```sh
  mkdir -p temp; cd temp

  ../.build/llvm-obj/bin/opt \
    -crellvm-passwhitelist=mem2reg \
    ../crellvm-tests/csmith/ll-files/00001.ll \
    -o 00001.tgt.ll -S

  ../ocaml/main.native $SRC $TGT $PROOF
  ```


### Interactive Theorem Proving

`make proof-quick` generates `.vio` files, which is enough for interactive theorem proving (either
in CoqIDE or ProofGeneral).

`coq/status-proof.sh` to grep all assumption keywords (e.g. `admit`, `Axiom`) in the Coq files.
Currently it reports several admits, all of which are either (1) OCaml utility functions that are
not relevant to the correctness of the proof checker, (2) functions that are implemented in OCaml
for performance reasons, or (3) axioms on the external functions.


### Test

- `make test-init`: Downloads benchmark programs.

- `make test-update`: Updates benchmark programs.

- `make test`: Performs benchmark (§7).

    + The benchmark programs (§7. "Benchmarks") are in the following directories: SPEC CINT2006 C
      Benchmarks in `crellvm-tests/speccpu2006-ll`; LLVM nightly test suite in
      `crellvm-tests/LNT-ll`; the five open-source C projects in `crellvm-tests/gnu-projects-ll`.
    
      1000 randomly-generated C files (§7. "Validating Randomly Generated Programs") are in
      `crellvm-tests/csmith/ll-files`.
    
      FYI, `crellvm-tests/BENCHMARKS.md` explains how to extract `.ll` files from the benchmark
      programs.

    + `make test` executes `crellvm-tests/run-benchmark.sh`, which in turn executes
      `crellvm-tests/crellvm-tests-parallel/src/main/scala/main.scala`. `scala .../main.scala -h`:
      Gives a manual for the internal script:

        * `-j $CORE`: number of cores used for testing.
        * `-a $OPTION`: options to be passed to `opt`, e.g. `-O2`.
        * `-i $TESTDIR`: the address of the benchmark you want to compile and validate.

    + For example, `scala .../main.scala -j 8 -a "-O2" -i crellvm-tests/LNT-ll` means:

        * Execute `opt` (proof-generating LLVM IR optimizer) and `main.native` (ERHL proof checker)
          for each `.ll` files in `crellvm-tests/LNT-ll`.

        * The test result (files `report.summary`, `report.generate`, `report.validate`) will be in
          the `./test_result.LNT-ll.0` directory.
