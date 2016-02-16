Require Import sflib.

Require Import vellvm.

Require Import syntax_ext.

Definition is_general_call (ocmd: option cmd) (retid: id) : Prop :=
  match ocmd with
    | Some (insn_call rid _ _ _ _ _ _) => rid = retid
    | _ => False
  end.

Definition is_general_call_state (st: Opsem.State) : Prop :=
  match st with
    | Opsem.mkState ec ecs _ =>
      match ec with
        | Opsem.mkEC _ _ (ccmd::ccmds) _ _ _ =>
          match ccmd with
            | insn_call _ _ _ _ _ _ _ => True
            | _ => False
          end
        | _ => False
      end
  end.

Definition is_call_readonly m (st: Opsem.State) : Prop :=
  match st with
    | Opsem.mkState ec ecs _ =>
      match ec with
        | Opsem.mkEC _ _ (ccmd::ccmds) _ _ _ =>
          match ccmd with
            | insn_call _ _ _ _ _ fv _ =>
              match fv with
                | value_id f
                | value_const (const_gid _ f) =>
                  (match (lookupFdecViaIDFromModule m f) with
                     | Some (fdec_intro (fheader_intro
                       (fnattrs_intro _ _ _ _ a) _ _ _ _) _)
                       => (in_dec attribute_dec attribute_readnone a \/
                         in_dec attribute_dec attribute_readonly a)
                     | _ => False
                   end) \/
                  (match (lookupFdefViaIDFromModule m f) with
                     | Some (fdef_intro (fheader_intro
                       (fnattrs_intro _ _ _ _ a) _ _ _ _) _)
                       => (in_dec attribute_dec attribute_readnone a \/
                         in_dec attribute_dec attribute_readonly a)
                     | _ => False
                   end)
                | _ => False
              end
            | _ => False
          end
        | _ => False
      end
  end.

Definition is_call cfg (st: Opsem.State) tfid : Prop :=
  match st with
    | Opsem.mkState ec ecs _ =>
      match ec with
        | Opsem.mkEC _ _ (ccmd::ccmds) _ _ _ =>
          match ccmd with
            | insn_call _ _ _ _ _ fv _ =>
              exists fptrs, exists fptr, exists fd,
                Opsem.getOperandValue (OpsemAux.CurTargetData cfg) fv (Opsem.Locals ec) (OpsemAux.Globals cfg) =
                Some fptrs /\
                fptr @ fptrs /\
                OpsemAux.lookupFdefViaPtr (OpsemAux.CurProducts cfg) (OpsemAux.FunTable cfg) fptr = Some fd /\
                getFdefID fd = tfid
            | _ => False
          end
        | _ => False
      end
  end.

Lemma is_call_or_not: forall cfg (st: Opsem.State)
  (Hstep: exists nst, exists tr, Opsem.sInsn cfg st nst tr),
  (exists tfid, is_call cfg st tfid) \/ (forall tfid, ~ is_call cfg st tfid).
Proof.
  i. unfold is_call.
  destruct st.
  destruct ECS. try (by right).
  destruct EC. destruct CurCmds; try (by right).
  destruct c; try (by right).
  destruct Hstep as [nst [tr Hstep']].
  inversion Hstep'; simpl.
  - left.
    exists fid; exists fptrs; exists fptr;
    exists (fdef_intro (fheader_intro fa rt fid la va) lb).
    splits; try done.
  - right. intros tfid [fptrs0 [fptr0 [fd [Hfptrs [Hfptr [Hlookup Hfid]]]]]].
    rewrite H17 in Hfptrs. inv Hfptrs.
    inv Hfptr. inv H18.
    unfold OpsemAux.lookupExFdecViaPtr in H19.
    unfold OpsemAux.lookupFdefViaPtr in Hlookup.
    remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptrs0) as fn.
    destruct fn as [fnid|]; [inv H19|by inv H19].
    inv Hlookup.
    by rewrite H1 in H0.
  - destruct EC. destruct CurCmds; try (by right).
    destruct c; try (by right).
    destruct Hstep as [nst [tr Hstep']].
    inversion Hstep'; simpl.
    + left.
      exists fid. exists fptrs; exists fptr;
      exists (fdef_intro (fheader_intro fa rt fid la va) lb).
      splits; try done.
    + right.
      intros tfid [fptrs0 [fptr0 [fd [Hfptrs [Hfptr [Hlookup Hfid]]]]]].
      rewrite H17 in Hfptrs. inv Hfptrs.
    inv Hfptr. inv H18.
    unfold OpsemAux.lookupExFdecViaPtr in H19.
    unfold OpsemAux.lookupFdefViaPtr in Hlookup.
    remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptrs0) as fn.
    destruct fn as [fnid|]; [inv H19|by inv H19].
    inv Hlookup.
    by rewrite H1 in H0.
Qed.

Definition is_excall cfg (st: Opsem.State) : Prop :=
  match st with
    | Opsem.mkState ec ecs _ =>
      match ec with
        | Opsem.mkEC _ _ (ccmd::ccmds) _ _ _ =>
          match ccmd with
            | insn_call _ _ _ _ _ fv _ =>
              exists fptrs, exists fptr, exists fd,
                Opsem.getOperandValue (OpsemAux.CurTargetData cfg) fv (Opsem.Locals ec) (OpsemAux.Globals cfg) =
                Some fptrs /\
                fptr @ fptrs /\
                OpsemAux.lookupExFdecViaPtr (OpsemAux.CurProducts cfg) (OpsemAux.FunTable cfg) fptr = Some fd
            | _ => False
          end
        | _ => False
      end
  end.

Lemma is_excall_or_not: forall cfg st
  (Hstep: exists nst, exists tr, Opsem.sInsn cfg st nst tr),
  (is_excall cfg st) \/ (~ is_excall cfg st).
Proof.
  i; unfold is_excall.
  destruct st.
  destruct ECS; try (by right).
  destruct EC; destruct CurCmds; try (by right).
  destruct c; try (by right).
  destruct Hstep as [nst [tr Hstep']].
  inversion Hstep'.
  - right. intros [fptrs0 [fptr0 [fd [Hfptrs [Hfptr Hlookup]]]]].
    simpl in *; rewrite H17 in Hfptrs; inversion Hfptrs;
    inversion Hfptr; inversion H18.
    subst fptrs fptrs0 fptr0; clear Hfptrs.
    clear -H19 Hlookup.
    unfold OpsemAux.lookupFdefViaPtr in H19.
    unfold OpsemAux.lookupExFdecViaPtr in Hlookup.
    remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as fn.
    destruct fn as [fnid|]; try (inversion Hlookup; fail).
    inversion H19; inversion Hlookup.
    rewrite H0 in H1; done.
  - left.
    exists fptrs; exists fptr;
      exists (fdec_intro (fheader_intro fa rt fid la va) dck).
    splits; try done.
  - destruct EC; destruct CurCmds; try (by right).
    destruct c; try (by right).
    destruct Hstep as [nst [tr Hstep']].
    inversion Hstep'.
    + right. intros [fptrs0 [fptr0 [fd [Hfptrs [Hfptr Hlookup]]]]].
      simpl in *; rewrite H17 in Hfptrs; inversion Hfptrs;
      inversion Hfptr; inversion H18.
      subst fptrs fptrs0 fptr0; clear Hfptrs.
      clear -H19 Hlookup.
      unfold OpsemAux.lookupFdefViaPtr in H19.
      unfold OpsemAux.lookupExFdecViaPtr in Hlookup.
      remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as fn.
      destruct fn as [fnid|]; try (inversion Hlookup; fail).
      inversion H19; inversion Hlookup.
      rewrite H0 in H1; done.
    + left.
      exists fptrs; exists fptr;
      exists (fdec_intro (fheader_intro fa rt fid la va) dck).
      splits; try done.
Qed.

Lemma is_call_is_excall_contradiction: forall cfg st fid
  (Hstep: exists nst, exists tr, Opsem.sInsn cfg st nst tr)
  (Hcontr: is_call cfg st fid /\ is_excall cfg st),
  False.
Proof.
  intros cfg st fid [nst [tr Hstep']] [Hcall Hexcall].
  destruct st.
  destruct ECS; try done.
  destruct EC; destruct CurCmds; try done.
  destruct c; try done.
  simpl in *.
  inversion Hcall as [fptrs1 [fptr1 [fd1 [Hfptrs1 [Hfptr1 [Hlookup1 _]]]]]];
    clear Hcall.
  inversion Hexcall as [fptrs2 [fptr2 [fd2 [Hfptrs2 [Hfptr2 Hlookup2]]]]];
    clear Hexcall.
  rewrite Hfptrs1 in Hfptrs2; inversion Hfptrs2; subst.
  inversion Hfptr2; subst.
  inversion Hfptr1; subst.
  clear -Hlookup1 Hlookup2.
  unfold OpsemAux.lookupExFdecViaPtr in Hlookup2.
  unfold OpsemAux.lookupFdefViaPtr in Hlookup1.
  remember (OpsemAux.lookupFdefViaGVFromFunTable (OpsemAux.FunTable cfg) fptrs2) as fn.
  destruct fn as [fnid|]; try (inversion Hlookup2; fail).
  inversion Hlookup2; inversion Hlookup1.
  rewrite H1 in H0; done.
  destruct EC. destruct CurCmds; try done.
  destruct c; try done.
  simpl in *.
  inversion Hcall as [fptrs1 [fptr1 [fd1 [Hfptrs1 [Hfptr1 [Hlookup1 _]]]]]];
    clear Hcall.
  inversion Hexcall as [fptrs2 [fptr2 [fd2 [Hfptrs2 [Hfptr2 Hlookup2]]]]];
    clear Hexcall.
  rewrite Hfptrs1 in Hfptrs2; inversion Hfptrs2; subst.
  inversion Hfptr2; subst.
  inversion Hfptr1; subst.
  clear -Hlookup1 Hlookup2.
  unfold OpsemAux.lookupExFdecViaPtr in Hlookup2.
  unfold OpsemAux.lookupFdefViaPtr in Hlookup1.
  remember (OpsemAux.lookupFdefViaGVFromFunTable (OpsemAux.FunTable cfg) fptrs2) as fn.
  destruct fn as [fnid|]; try (inversion Hlookup2; fail).
  inversion Hlookup2; inversion Hlookup1.
  rewrite H1 in H0; done.
Qed.

Lemma not_is_excall_implies_tr_nil: forall cfg st
  (Hnexc: ~ is_excall cfg st)
  (Hstep: exists ns, exists tr, Opsem.sInsn cfg st ns tr),
  exists ns, Opsem.sInsn cfg st ns E0.
Proof.
  intros cfg st Hnexc [ns [tr Hstep]].
  unfold is_excall in Hnexc.
  destruct st; destruct ECS; try (inversion Hstep; fail).
  destruct EC; destruct CurCmds;
    try (inversion Hstep; exists ns; subst; done; fail).
  destruct c; try (inversion Hstep; exists ns; subst; done; fail).
  inversion Hstep; try (exists ns; subst; done; fail).
  subst; simpl in Hnexc.
  elim Hnexc; exists fptrs; exists fptr;
    exists (fdec_intro (fheader_intro fa rt fid la va) dck).
  done.
  destruct EC; destruct CurCmds;
    try (inversion Hstep; exists ns; subst; done; fail).
  destruct c; try (inversion Hstep; exists ns; subst; done; fail).
  inversion Hstep; try (exists ns; subst; done; fail).
  subst; simpl in Hnexc.
  elim Hnexc; exists fptrs; exists fptr;
    exists (fdec_intro (fheader_intro fa rt fid la va) dck).
  done.
Qed.

Definition is_return (st: Opsem.State) : Prop :=
  match st with
    | Opsem.mkState ec ecs _ =>
      (Opsem.CurCmds ec) = nil /\
      match (Opsem.Terminator ec) with
        | insn_return _ _ _ => True
        | insn_return_void _ => True
        | _ => False
      end
  end.

Lemma is_return_implies_tr_nil: forall cfg st
  (Hret: is_return st)
  (Hstep: exists ns, exists tr, Opsem.sInsn cfg st ns tr),
  exists ns, Opsem.sInsn cfg st ns E0.
Proof.
  intros.
  inversion Hstep as [ns [tr Hstep']]; clear Hstep.
  exists ns.
  unfold is_return in Hret.
  destruct st; destruct ECS; try done.
  destruct EC; destruct Hret as [Hcc Hterm]; simpl in *; subst.
  inversion Hstep'; subst; done.
  destruct EC; destruct Hret as [Hcc Hterm]; simpl in *; subst.
  inversion Hstep'; subst; done.
Qed.

Definition is_branch cfg (st: Opsem.State) bid : Prop :=
  match st with
    | Opsem.mkState ec ecs _ =>
      (Opsem.CurCmds ec) = nil /\
      match (Opsem.Terminator ec) with
        | insn_br _ cond l1 l2 =>
          exists conds, exists c,
            (getOperandValue (OpsemAux.CurTargetData cfg) cond (Opsem.Locals ec) (OpsemAux.Globals cfg) = Some conds /\
              c @ conds /\
              (if isGVZero (OpsemAux.CurTargetData cfg) c then bid = l2 else bid = l1))
        | insn_br_uncond _ l => bid = l
        | _ => False
      end
  end.

Lemma is_branch_implies_tr_nil: forall cfg st
  (Hbrc: exists bid, is_branch cfg st bid)
  (Hstep: exists ns, exists tr, Opsem.sInsn cfg st ns tr),
  exists ns, Opsem.sInsn cfg st ns E0.
Proof.
  intros.
  inversion Hstep as [ns [tr Hstep']]; clear Hstep.
  inversion Hbrc as [bid Hbrc']; clear Hbrc.
  exists ns.    
  unfold is_branch in Hbrc'.
  destruct st; destruct ECS; try done.
  destruct EC; destruct Hbrc' as [Hcc Hterm]; simpl in *; subst.
  inversion Hstep'; subst; done.
  destruct EC; destruct Hbrc' as [Hcc Hterm]; simpl in *; subst.
  inversion Hstep'; subst; done.
Qed.

Lemma ret_pop_terminator_implies_return_or_branch:
  forall cfg ps ec ecs ccmds cn
    (Hstep: exists ns, exists tr, Opsem.sInsn cfg ps ns tr)
    (Hecs: Opsem.ECS ps = ec::ecs)
    (Hst: Opsem.CurCmds ec = ccmds)
    (Hrt: ret_pop_terminator = pop_one_X ccmds cn),
    (is_return ps) \/ (exists bid, is_branch cfg ps bid).
Proof.
  intros.
  
  unfold pop_one_X in Hrt.
  destruct (noop_idx_zero_exists cn); try (inversion Hrt; fail).
  destruct ccmds; try (inversion Hrt; fail); clear Hrt.
  
  destruct ec; simpl in Hst; subst.
  destruct Terminator; destruct ps; simpl in Hecs.

  - left. unfold is_return.
    destruct ECS. 
    + inv Hecs.
    + inv Hecs. split. admit. admit. 
 
  - left.
  unfold is_return; subst; simpl; split; auto. admit. admit.

  - right. admit.
  (*subst; inversion Hstep as [ns [tr Hstep']]; inversion Hstep'.
  exists (if isGVZero TD c then l2 else l1).
  simpl; split; auto.
  exists conds; exists c.
  split; auto.
  split; auto.
  destruct (isGVZero TD c); auto.*) 

  - right. admit.
  (* subst; inversion Hstep as [ns [tr Hstep']]; inversion Hstep'.
  exists l5.
  simpl; split; auto.*)

  - elimtype False.
  subst; simpl. admit.
  (*inversion Hstep as [ns [tr Hstep']]; inversion Hstep'.*)
Admitted.
