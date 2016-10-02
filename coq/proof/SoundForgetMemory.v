Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import opsem.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import Exprs.
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundForget.

Set Implicit Arguments.


Definition noalias_with_def_memory (conf:Config) (def_memory:option (GenericValue * typ)) (ptr:GenericValue) (ty:typ): Prop :=
  forall gptr_def ty_def
         (DEF: def_memory = Some (gptr_def, ty_def)),
    InvState.Unary.sem_noalias conf gptr_def ptr ty_def ty.

Inductive mem_change : Type :=
| mem_change_alloc
    (gsz:sz) (gn:GenericValue) (a:align)
| mem_change_store
    (ptr:GenericValue) (ty:typ) (gv:GenericValue) (a:align)
| mem_change_free
    (ptr:GenericValue)
| mem_change_none
.

(* Definition ptr_to_genericvalue conf st invst ptr: option (GenericValue * typ) := *)
(*   match InvState.Unary.sem_valueT conf st invst ptr.(fst) with *)
(*   | Some gv => Some (gv, ptr.(snd)) *)
(*   | None => None *)
(*   end. *)

Inductive mem_change_inject mi: mem_change -> mem_change -> Prop :=
| mem_change_inject_alloc_alloc
    gsz gn a
  : mem_change_inject mi (mem_change_alloc gsz gn a) (mem_change_alloc gsz gn a)
| mem_change_inject_alloc_none
    gsz gn a
  : mem_change_inject mi (mem_change_alloc gsz gn a) mem_change_none
| mem_change_inject_none_alloc
    gsz gn a
  : mem_change_inject mi mem_change_none (mem_change_alloc gsz gn a)
| mem_change_inject_store
    ptr0 ptr1 gv0 gv1 ty a
    (PTR_INJECT: genericvalues_inject.gv_inject mi ptr0 ptr1)
    (VAL_INJECT: genericvalues_inject.gv_inject mi gv0 gv1)
  : mem_change_inject mi (mem_change_store ptr0 ty gv0 a) (mem_change_store ptr1 ty gv1 a)
| mem_change_inject_free
    ptr0 ptr1
    (PTR_INJECT: genericvalues_inject.gv_inject mi ptr0 ptr1)
    : mem_change_inject mi (mem_change_free ptr0) (mem_change_free ptr1)
| mem_change_inject_none
    : mem_change_inject mi mem_change_none mem_change_none
.

Inductive mem_change_location conf st invst: mem_change -> option Ptr.t -> Prop :=
| mem_change_location_alloc
    bsz gn a
  : mem_change_location conf st invst (mem_change_alloc bsz gn a) None
| mem_change_location_store
    ptr gv_ptr gv a
    (STORE_PTR: InvState.Unary.sem_valueT conf st invst ptr.(fst) = Some gv_ptr)
  : mem_change_location conf st invst (mem_change_store gv_ptr ptr.(snd) gv a) (Some ptr)
| mem_change_location_free
    ptr gv_ptr
    (FREE_PTR: InvState.Unary.sem_valueT conf st invst ptr.(fst) = Some gv_ptr)
  : mem_change_location conf st invst (mem_change_free gv_ptr) (Some ptr)
| mem_change_location_none
  : mem_change_location conf st invst mem_change_none None
.

Inductive mem_change_equiv (conf:Config) (mem0 mem1:mem): mem_change -> Prop :=
| mem_change_equiv_alloc
    mb bsz gn a
    (MALLOC: Some (mem1, mb) = malloc conf.(CurTargetData) mem0 bsz gn a)
  : mem_change_equiv conf mem0 mem1 (mem_change_alloc bsz gn a)
| mem_change_equiv_store
    ptr ty gv a
    (STORE: Some mem1 = mstore conf.(CurTargetData) mem0 ptr ty gv a)
  : mem_change_equiv conf mem0 mem1 (mem_change_store ptr ty gv a)
| mem_change_equiv_free
    ptr
    (FREE: Some mem1 = free conf.(CurTargetData) mem0 ptr)
  : mem_change_equiv conf mem0 mem1 (mem_change_free ptr)
| mem_change_equiv_none
    (MEM: mem0 = mem1)
  : mem_change_equiv conf mem0 mem1 mem_change_none
.

Inductive state_equiv_except_mem (conf:Config) (st0 st1:State) (mem_chng:mem_change) :=
| state_equiv_except_mem_intro
    (LOCALS_EQ: st0.(EC).(Locals) = st1.(EC).(Locals))
    (MEM_CHANGE_EQUIV: mem_change_equiv conf st0.(Mem) st1.(Mem) mem_chng)
.

Definition unique_preserved_mem conf st inv: Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true),
    InvState.Unary.sem_unique conf st u.

(* Definition ptr_to_genericvalue conf st invst ptr: option (GenericValue * typ) := *)
(*   match InvState.Unary.sem_valueT conf st invst ptr.(fst) with *)
(*   | Some gv => Some (gv, ptr.(snd)) *)
(*   | None => None *)
(*   end. *)

Lemma forget_memory_unary_sound1
      conf st0 invst0 invmem0 inv0
      def_memory st1 public gmax mem_change
        (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
        (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
        (MEM_EQUIV: state_equiv_except_mem conf st0 st1 mem_change)
        (MEM_CHANGE: mem_change_location conf st0 invst0 mem_change (Some def_memory))
        (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0)
    : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 (ForgetMemory.unary def_memory inv0)>> /\
      <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>.
Proof.
Admitted.

Lemma forget_memory_unary_sound2
      conf st0 st1 mem_change
      invst0 invmem0 inv0 gmax public
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (MEM_EQUIV : state_equiv_except_mem conf st0 st1 mem_change)
      (MEM_CHANGE : mem_change_location conf st0 invst0 mem_change None)
      (TGT : InvState.Unary.sem conf st0 invst0 invmem0 inv0)
  : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 inv0>> /\
    <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>.
Proof.
Admitted.

Lemma some_injective A (a b:A):
  Some a = Some b -> a = b.
Proof.
  congruence.
Qed.

Lemma mem_inject_change
      conf_src mem0_src mem1_src mem_change_src
      conf_tgt mem0_tgt mem1_tgt mem_change_tgt
      mi
      (MEM_CHANGE_EQUIV_SRC : mem_change_equiv conf_src mem0_src mem1_src mem_change_src)
      (MEM_CHANGE_EQUIV_TGT : mem_change_equiv conf_tgt mem0_tgt mem1_tgt mem_change_tgt)
      (MEM_CHANGE_INJECT : mem_change_inject mi mem_change_src mem_change_tgt)
      (INJECT : Memory.Mem.inject mi mem0_src mem0_tgt)
  : Memory.Mem.inject mi mem1_src mem1_tgt.
Proof.
  inv MEM_CHANGE_INJECT.
  - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold malloc in *.
    apply some_injective in MALLOC.
    apply some_injective in MALLOC0.
    econs.
    + eapply Memory.Mem.alloc_right_inj; eauto.
      eapply Memory.Mem.alloc_left_unmapped_inj; eauto.
      apply mi_freeblocks.
      eapply Memory.Mem.fresh_block_alloc; eauto.
    + i. apply mi_freeblocks. ii.
      exploit Memory.Mem.valid_block_alloc; try (symmetry; exact MALLOC); eauto.
    + ii. exploit mi_mappedblocks; eauto. i.
      eapply Memory.Mem.valid_block_alloc; eauto.
    + ii. exploit mi_no_overlap; eauto.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
    + ii. exploit mi_representable; eauto. des.
      * left.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * right.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
  - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold malloc in *.
    apply some_injective in MALLOC.
    econs.
    + eapply Memory.Mem.alloc_left_unmapped_inj; eauto.
      apply mi_freeblocks.
      eapply Memory.Mem.fresh_block_alloc; eauto.
    + i. apply mi_freeblocks. ii.
      exploit Memory.Mem.valid_block_alloc; try (symmetry; exact MALLOC); eauto.
    + ii. exploit mi_mappedblocks; eauto.
    + ii. exploit mi_no_overlap; eauto.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
    + ii. exploit mi_representable; eauto. des.
      * left.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * right.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
  - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold malloc in *.
    apply some_injective in MALLOC.
    econs.
    + eapply Memory.Mem.alloc_right_inj; eauto.
    + i. apply mi_freeblocks. eauto.
    + ii. exploit mi_mappedblocks; eauto. i.
      eapply Memory.Mem.valid_block_alloc; eauto.
    + ii. exploit mi_no_overlap; eauto.
    + ii. exploit mi_representable; eauto.
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold mstore in *. des_ifs.
    (* exploit genericvalues_inject.mem_inj_mstore_aux; eauto. *)
    
    (* Memory.Mem.mem_inj *)
    (*   memory_sim.MoreMem.mem_inj *)
    admit. (* store - store *)
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold free in *. des_ifs.
    eapply Memory.Mem.free_left_inject; eauto.
    eapply Memory.Mem.free_right_inject; eauto.
    admit. (* free - free *)
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    econs; eauto.
Admitted.

Lemma forget_memory_sound
      conf_src st0_src st1_src def_memory_src mem_change_src
      conf_tgt st0_tgt st1_tgt def_memory_tgt mem_change_tgt
      invst0 invmem0 inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (MEM_EQUIV_SRC: state_equiv_except_mem
                        conf_src
                        st0_src st1_src
                        mem_change_src)
      (MEM_EQUIV_TGT: state_equiv_except_mem
                        conf_tgt
                        st0_tgt st1_tgt
                        mem_change_tgt)
      (MEM_CHANGE_SRC: mem_change_location conf_src st0_src invst0.(InvState.Rel.src) mem_change_src def_memory_src)
      (MEM_CHANGE_TGT: mem_change_location conf_tgt st0_tgt invst0.(InvState.Rel.tgt) mem_change_tgt def_memory_tgt)
      (MEM_CHANGE_INJECT: mem_change_inject invmem0.(InvMem.Rel.inject) mem_change_src mem_change_tgt)
      (UNIQUE_PRSV_SRC: unique_preserved_mem conf_src st1_src inv0.(Invariant.src))
      (UNIQUE_PRSV_TGT: unique_preserved_mem conf_tgt st1_tgt inv0.(Invariant.tgt))
  : <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0
                              (ForgetMemory.t def_memory_src def_memory_tgt inv0) >> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0>>.
Proof.
  inv STATE.
  unfold ForgetMemory.t.
  destruct def_memory_src as [[]|], def_memory_tgt as [[]|]; ss.
  inv MEM.

  - exploit forget_memory_unary_sound1; try exact SRC; eauto. i. des.
    exploit forget_memory_unary_sound1; try exact TGT; eauto. i. des.
    splits.
    + econs; ss; eauto. i.
      hexploit MAYDIFF; eauto. i.
      ii. exploit H.
      { destruct id0 as [[]]; eauto.
        inv MEM_EQUIV_SRC; solve_sem_idT.
        rewrite -> LOCALS_EQ; eauto.
      }
      i. des.
      esplits; eauto.
      destruct id0 as [[]]; eauto.
      inv MEM_EQUIV_TGT;
        solve_sem_idT; rewrite <- LOCALS_EQ; eauto.
    + econs; ss; eauto.
      inv MEM_EQUIV_SRC.
      inv MEM_EQUIV_TGT.

      eapply mem_inject_change; eauto.
      
  - inv MEM.
    exploit forget_memory_unary_sound1; try exact SRC; eauto. i. des.
    exploit forget_memory_unary_sound2; try exact TGT; eauto. i. des.
    splits.
    + econs; ss; eauto.
      i.
      hexploit MAYDIFF; eauto. i.
      ii. exploit H.
      { destruct id0 as [[]]; eauto.
        inv MEM_EQUIV_SRC; solve_sem_idT.
        rewrite -> LOCALS_EQ; eauto.
      }
      i. des.
      esplits; eauto.
      destruct id0 as [[]]; eauto.
      inv MEM_EQUIV_TGT;
        solve_sem_idT; rewrite <- LOCALS_EQ; eauto.
    + econs; ss; eauto.
      inv MEM_EQUIV_SRC.
      inv MEM_EQUIV_TGT.
      eapply mem_inject_change; eauto.
  - inv MEM.
    exploit forget_memory_unary_sound2; try exact SRC; eauto. i. des.
    exploit forget_memory_unary_sound1; try exact TGT; eauto. i. des.
    splits.
    + econs; ss; eauto.
      i.
      hexploit MAYDIFF; eauto. i.
      ii. exploit H.
      { destruct id0 as [[]]; eauto.
        inv MEM_EQUIV_SRC; solve_sem_idT.
        rewrite -> LOCALS_EQ; eauto.
      }
      i. des.
      esplits; eauto.
      destruct id0 as [[]]; eauto.
      inv MEM_EQUIV_TGT;
        solve_sem_idT; rewrite <- LOCALS_EQ; eauto.
    + econs; ss; eauto.
      inv MEM_EQUIV_SRC.
      inv MEM_EQUIV_TGT.
      eapply mem_inject_change; eauto.
  - inv MEM.
    exploit forget_memory_unary_sound2; try exact SRC; eauto. i. des.
    exploit forget_memory_unary_sound2; try exact TGT; eauto. i. des.
    splits.
    + econs; ss; eauto.
      i.
      hexploit MAYDIFF; eauto. i.
      ii. exploit H.
      { destruct id0 as [[]]; eauto.
        inv MEM_EQUIV_SRC; solve_sem_idT.
        rewrite -> LOCALS_EQ; eauto.
      }
      i. des.
      esplits; eauto.
      destruct id0 as [[]]; eauto.
      inv MEM_EQUIV_TGT;
        solve_sem_idT; rewrite <- LOCALS_EQ; eauto.
    + econs; ss; eauto.
      inv MEM_EQUIV_SRC.
      inv MEM_EQUIV_TGT.
      eapply mem_inject_change; eauto.
Admitted.
