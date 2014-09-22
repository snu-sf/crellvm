Require Import vgtac.

Require Import vellvm.
Require Import hint_sem.
Import Opsem.

Axiom callExternalOrIntrinsics_prop_1 :
  forall td gl mem fid rt la dck gvs oresult tr mem'
    (H: callExternalOrIntrinsics td gl mem fid rt la dck gvs = ret (oresult, tr, mem')),
    Mem.nextblock mem <= Mem.nextblock mem'.  

Axiom callExternalOrIntrinsics_prop_2 :
  forall
    alpha gmax
    TD id typ typargs deckind
    gl1 mem1 gvs1
    gl2 mem2 gvs2
    li1 pi1 allocas1 li2 pi2 allocas2
    (Hgl: globals_equivalent alpha gmax gl1 gl2)
    (Hvm: valid_memories alpha gmax mem1 mem2 li1 li2 pi1 pi2)
    (Hal: valid_allocas mem1 mem2 allocas1 allocas2)
    (Hwf: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
    (Hgvs: genericvalues_inject.gv_list_inject alpha gvs1 gvs2)
    oresult1 tr mem1' (H1: ret (oresult1, tr, mem1') = callExternalOrIntrinsics TD gl1 mem1 id typ typargs deckind gvs1),
    exists oresult2, exists mem2',
      ret (oresult2, tr, mem2') = callExternalOrIntrinsics TD gl2 mem2 id typ typargs deckind gvs2 /\
      valid_memories alpha gmax mem1' mem2' li1 li2 pi1 pi2 /\
      valid_allocas mem1' mem2' allocas1 allocas2 /\
      (forall result1 (Hresult1: ret result1 = oresult1),
        exists result2,
          ret result2 = oresult2 /\
          genericvalues_inject.gv_inject alpha result1 result2).

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
