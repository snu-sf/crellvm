Require Import vgtac.

Require Import vellvm.
Require Import program_sim.

Require Import state_props.
Require Import syntax_ext.

(* Additional definitions for logical semantics. *)
Definition noop_stack_t : Type := list noop_t.
Definition new_alloca_t : Type := option id.

Definition lookupALOpt X (m:AssocList (list X)) (i:atom) :=
  match lookupAL _ m i with
    | Some l => l
    | None => nil
  end.

Notation GVs := DGVs.(GVsT).
Definition lookupALExt (lc_old lc_new:@Opsem.GVsMap DGVs) (x:id_ext) : option GVs :=
  match x with
    | (i,ntag_old) => lookupAL _ lc_old i
    | (i,ntag_new) => lookupAL _ lc_new i
  end.

Section LogicalStep.
  Variable (cfg: OpsemAux.Config) (fn_al: products_noop_t).

  Definition ocons {A} (hd: option A) (tl: list A) : list A :=
    match hd with
      | Some a => a :: tl
      | _ => tl
    end.

  Definition get_noop_by_fid_bb fid bid : noop_t :=
    get_noop_by_bb bid (lookupALOpt _ fn_al fid).
  
  Definition pop_state_ocmd (st: @Opsem.ECStack DGVs) ns ocmd : Prop :=
    match st, ns with
      | ec::_, hn::_ =>
        match (pop_one_X (Opsem.CurCmds ec) hn) with
          | ret_pop_cmd ocmd' _ _ => ocmd = ocmd'
          | _ => False
        end
      | _, _ => False
    end.

  Definition pop_state_terminator (st: @Opsem.ECStack DGVs) ns : Prop :=
    match st, ns with
      | ec::_, hn::_ =>
        match (pop_one_X (Opsem.CurCmds ec) hn) with
          | ret_pop_terminator => True
          | _ => False
        end
      | _, _ => False
    end.

  Inductive pop_state : Set :=
  | pop_noop
  | pop_cmd
  | pop_terminator.

  Inductive pop_one (ccmds: list cmd) hpn pst hnn (na: new_alloca_t) : Prop :=
  | pop_one_cmd :
    forall rcmd lcmds
      (Hpop: pop_one_X ccmds hpn = ret_pop_cmd rcmd lcmds hnn)
      (Hist: pst = match rcmd with | None => pop_noop | _ => pop_cmd end)
      (Hna: na = match rcmd with
                   | Some (insn_alloca aid _ _ _) => ret aid
                   | Some (insn_malloc aid _ _ _) => ret aid
                   | _ => merror
                 end),
      pop_one ccmds hpn pst hnn na
  | pop_one_terminator :
    forall
      (Hpop: pop_one_X ccmds hpn = ret_pop_terminator)
      (Hist: pst = pop_terminator)
      (Hna: na = merror),
      pop_one ccmds hpn pst hnn na.

  Inductive logical_semantic_step_noop_cmd
    (ps: @Opsem.State DGVs) (pst: pop_state) (nnn: option noop_t) : Prop :=
  | logical_semantic_step_noop_cmd_noop
    (Hrcmd: pst = pop_noop)
    (Hnnn: nnn = None)
  | logical_semantic_step_noop_cmd_cmd
    (Hrcmd: pst = pop_cmd)
    (Hncall: ~ is_general_call_state ps)
    (Hnnn: nnn = None)
  | logical_semantic_step_noop_cmd_call fid fdef bid stmts
    (Hrcmd: pst = pop_cmd)
    (Hcall: is_call cfg ps fid)
    (Hfdef: ret fdef = lookupFdefViaIDFromProducts (OpsemAux.CurProducts cfg) fid)
    (Hbid: ret (bid, stmts) = getEntryBlock fdef)
    (Hnnn: nnn = Some (get_noop_by_fid_bb fid bid))
  | logical_semantic_step_noop_cmd_excall
    (Hrcmd: pst = pop_cmd)
    (Hexcall: is_excall cfg ps)
    (Hnnn: nnn = None).

  Inductive logical_semantic_step_noop_terminator 
    (ps: @Opsem.State DGVs) (ec: @Opsem.ExecutionContext DGVs) 
    (nnn: option noop_t) : Prop :=
  | logical_semantic_step_noop_terminator_ret
    (Hret: is_return ps)
    (Hnnn: nnn = None)
  | logical_semantic_step_noop_terminator_brc bid
    (Hbrc: is_branch cfg ps bid)
    (Hnnn: nnn = Some (get_noop_by_fid_bb (getFdefID (Opsem.CurFunction ec)) bid)).

  Inductive logical_semantic_step_noop_stk
    (ps: @Opsem.State DGVs) tn ec pst hnn : noop_stack_t -> Prop :=
  | logical_semantic_step_noop_stk_cmd: 
    forall nnn
      (Hnnn: logical_semantic_step_noop_cmd ps pst nnn),
      logical_semantic_step_noop_stk ps tn ec pst hnn (ocons nnn (hnn::tn))
  | logical_semantic_step_noop_stk_term:
    forall nnn
      (Hpop: pst = pop_terminator)
      (Hnnn: logical_semantic_step_noop_terminator ps ec nnn),
      logical_semantic_step_noop_stk ps tn ec pst hnn (ocons nnn tn).

  Inductive logical_semantic_step ps ns pn nn na tr : Prop :=
  | logical_semantic_step_intro :
    forall ec ecs hpn tn pst hnn fn
      (Hec: Opsem.ECS ps = ec::ecs)
      (Hpn: pn = hpn::tn)
      (Hfn: lookupALOpt _ fn_al (getFdefID (Opsem.CurFunction ec)) = fn)
      (Hpop: pop_one (Opsem.CurCmds ec) hpn pst hnn na)
      (Hnoop: logical_semantic_step_noop_stk ps tn ec pst hnn nn)
      (Hstep: match pst with 
                | pop_noop => ns = ps /\ tr = E0 
                | _ => Opsem.sInsn cfg ps ns tr
              end),
      logical_semantic_step ps ns pn nn na tr.

  Lemma pop_state_ocmd_some_implies_logical_step_real_step:
    forall pec pecs necs pns nns pm nm na tr ccmd
      (Hpopst: pop_state_ocmd pecs pns (ret ccmd))
      (Hstep: logical_semantic_step
        {| Opsem.EC := pec; Opsem.ECS := pecs; Opsem.Mem := pm |}
        {| Opsem.EC := pec; Opsem.ECS := necs; Opsem.Mem := nm |} pns nns na tr),
      Opsem.sInsn cfg {| Opsem.EC := pec; Opsem.ECS := pecs; Opsem.Mem := pm |}
      {| Opsem.EC := pec; Opsem.ECS := necs; Opsem.Mem := nm |} tr.
  Proof.
    intros; inv Hstep.
    destruct pst; try done.
    simpl in Hec; inv Hec; clear H.
    unfold pop_state_ocmd in Hpopst.
    inv Hpop; try done.
    rewrite Hpop0 in Hpopst.
    destruct rcmd; done.
  Qed.

End LogicalStep.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
