open Infrastructure
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open Syntax
open Extraction_defs
open Vars_aux
open Dom_tree


type microhint_args = {
  lfdef : LLVMsyntax.fdef;
  lnoop : noop_t;
  rfdef : LLVMsyntax.fdef;
  rnoop : noop_t;
  left_m : LLVMsyntax.coq_module;
  right_m : LLVMsyntax.coq_module;
  fdef_hint : fdef_hint_t;
  dom_tree : AtomImpl.atom coq_DTree
}
