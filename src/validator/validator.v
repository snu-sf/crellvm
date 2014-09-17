Require Import vellvm.
Require Import decs.
Require Import syntax_ext.
Require Import hints.
Require Import basic_aux.
Require Import vars_aux.
Require Import validator_aux.
Require Import my_gvar_dec.

(** This validator checks if the two given programs (original and
optimized) have equivalent behavior (more specifically, having the
same observable behavior).

[valid_system] is the main validation procedure.  However, the real
meat is [valid_cmds].

[valid_cmds] checks if all post-conditions are implied by their
pre-conditions.  At the same time, it checks if two programs have
equivalent behavior.

[valid_cmd] checks by:
1) invariant_proceed: obtaining the strongest post-condition;
2) infrules_resolve: applying inference rules to canonize the
post-condition; and
3) invariant_implies: checking if the obtained post-condition implies
written post-condition.

The details are in validator_aux.v. *)

Definition valid_phis (m1 m2:module) (lphis rphis:phinodes) (prev_bb:l)
  (prehint posthint:insn_hint_t) : bool := 

  (* proceed *)
  match invariant_proceed_phis prehint lphis rphis prev_bb with
  | None => false
  | Some prehint' =>

  (* resolve infrules *)
  let prehint'' := infrules_resolve m1 m2 prehint' in

  invariant_implies prehint'' posthint
  end.

Fixpoint valid_AL_phis (m1 m2:module) (lphis rphis:phinodes) 
  (phis_AL_hint:AssocList insn_hint_t) (cmds_AL_hint:AssocList (list insn_hint_t)) 
  : bool :=
  match phis_AL_hint,cmds_AL_hint with
    | nil,nil => true
    | (prev_bb1,phis_hints)::phis_tl,(prev_bb2,cmds_hint::_)::cmds_tl =>
      l_dec prev_bb1 prev_bb2 &&
      valid_phis m1 m2 lphis rphis prev_bb1 phis_hints cmds_hint &&
      valid_AL_phis m1 m2 lphis rphis phis_tl cmds_tl
    | _,_ => false
  end.

Fixpoint valid_cmds (lm rm:module) (lcmds rcmds:list cmd) (lnoop rnoop:noop_t)
  (hints:list insn_hint_t) : bool :=

  match pop_one_X lcmds lnoop, pop_one_X rcmds rnoop, hints with
    | (ret_pop_cmd lcmd_opt next_lcmds next_lnoop),
      (ret_pop_cmd rcmd_opt next_rcmds next_rnoop),
      prehint::((posthint::tl) as next_hints) =>

      match invariant_proceed lm rm prehint lcmd_opt rcmd_opt with
      | None => false
      | Some prehint' =>

      let prehint'' := infrules_resolve lm rm prehint' in

      invariant_implies prehint'' posthint && 

      valid_cmds lm rm next_lcmds next_rcmds next_lnoop next_rnoop next_hints 
      end

    | ret_pop_terminator, ret_pop_terminator, _::nil => true

    | _, _, _ => false
  end.

Definition valid_AL_cmds (lm rm:module) (lcmds rcmds:list cmd) (lnoop rnoop:noop_t)
  (AL_hints:AssocList (list insn_hint_t)) : bool :=
  forallb
  (fun (one_AL_hint:id * list insn_hint_t) =>
    valid_cmds lm rm lcmds rcmds lnoop rnoop (snd one_AL_hint))
  AL_hints.

Fixpoint valid_term_edges (prev_bb:l) (prev_h:insn_hint_t) (bbs:list l) (all_hint:AssocList block_hint_t) : bool :=
  match bbs with
    | nil => true
    | cur_bb::tl => 
      match lookupAL _ all_hint cur_bb with
        | Some cur_bb_h =>
          match lookupAL _ (phi_hint cur_bb_h) prev_bb with
            | Some cur_first_h =>
              invariant_implies prev_h cur_first_h
            | _ => false
          end
        | _ => false
      end &&
      valid_term_edges prev_bb prev_h tl all_hint 
  end.

Definition valid_terms (m1 m2:module) (lterm rterm:terminator) (hint:insn_hint_t)
  (cur_bb:l) (all_hint:AssocList block_hint_t) : bool := 
  (terminator_args_eq_check lterm rterm hint) &&
  let next_bbs := get_all_nexts rterm in
  (* resolve infrules *)
  let hint' := infrules_resolve m1 m2 hint in
  valid_term_edges cur_bb hint' next_bbs all_hint.

Definition valid_cmds_to_term (cmds_hint:list insn_hint_t) (term_hint:insn_hint_t) : bool :=
  match last_hint cmds_hint with
    | Some prehint => invariant_implies prehint term_hint
    | _ => false
  end.

Definition valid_AL_cmds_to_term (cmds_AL_hint:AssocList (list insn_hint_t)) (term_hint:insn_hint_t) : bool :=
  forallb
  (fun (one_AL_hint:id * list insn_hint_t) => 
    valid_cmds_to_term (snd one_AL_hint) term_hint)
  cmds_AL_hint.

Definition valid_stmts (lm rm:module) (lstmts rstmts:stmts) (lnoop rnoop:noop_t)
  (hint:block_hint_t) (cur_bb:l) (all_hint:AssocList block_hint_t) 
  : bool :=
  match lstmts, rstmts with
    | stmts_intro lphis lcmds lters, stmts_intro rphis rcmds rters =>
      valid_AL_phis lm rm lphis rphis (phi_hint hint) (cmds_hint hint) &&
      valid_AL_cmds lm rm lcmds rcmds lnoop rnoop (cmds_hint hint) &&
      valid_AL_cmds_to_term (cmds_hint hint) (term_hint hint) &&
      valid_terms lm rm lters rters (term_hint hint) cur_bb all_hint
  end.

Definition valid_block (lm rm:module) (lb rb:block) (lnoop rnoop:noop_t)
  (all_hint:AssocList block_hint_t) : bool :=
  match lb, rb with
    | (ll,lstmts), (rl,rstmts) =>
      (id_dec ll rl) &&
      (match lookupAL _ all_hint ll with
         | None => false
         | Some block_hint =>
           valid_stmts lm rm lstmts rstmts 
             (get_noop_by_bb ll lnoop) (get_noop_by_bb ll rnoop)
             block_hint ll all_hint
       end)
  end.

Fixpoint valid_blocks (lm rm:module) (lbs rbs:blocks) (lnoop rnoop:noop_t)
  (hint:AssocList block_hint_t) : bool :=
  match lbs, rbs with
    | nil, nil => true
    | lb::lbs, rb::rbs =>
      valid_block lm rm lb rb lnoop rnoop hint && 
      valid_blocks lm rm lbs rbs lnoop rnoop hint
    | _, _ => false
  end.

Definition valid_initial_newdefs_eqs (e:eqs_t) : bool :=
    EqRegSetImpl.is_empty (eqs_eq_reg e) &&
    EqHeapSetImpl.is_empty (eqs_eq_heap e) &&
    NeqRegSetImpl.is_empty (eqs_neq_reg e).

Definition valid_initial_phi_hint (ph:insn_hint_t) : bool :=
  let inv_hint := hint_invariant ph in
    valid_initial_newdefs_eqs (invariant_original inv_hint) &&
    valid_initial_newdefs_eqs (invariant_optimized inv_hint) &&
    IdExtSetImpl.is_empty (iso_original inv_hint) &&
    IdExtSetImpl.is_empty (iso_optimized inv_hint)
    .

Definition is_empty {A} (l:list A) :=
  match l with nil => true | _ => false end.

Definition valid_initial_block (lbls rbls:blocks) (hint:fdef_hint_t) : bool :=
  match lbls,rbls with
    | ((ll,stmts_intro lphis _ _)::_), ((rl,stmts_intro rphis _ _)::_) => 
      l_dec ll rl &&
      is_empty lphis &&
      is_empty rphis &&
      match lookupAL _ (block_hints hint) ll with
        | Some {| phi_hint := (_,ph)::nil |} => valid_initial_phi_hint ph
        | _ => false
      end
    | _, _ => false
  end.

Definition valid_fdef (lm rm:module) (lfdef rfdef:fdef) (lnoop rnoop:noop_t) 
  (hint:fdef_hint_t) : bool :=
  match lfdef, rfdef with
    | fdef_intro lfh lbls, fdef_intro rfh rbls =>
      fheader_dec lfh rfh &&
      valid_initial_block lbls rbls hint &&
      valid_blocks lm rm lbls rbls lnoop rnoop (block_hints hint)
  end.

Fixpoint valid_products (lm rm:module) (lpds rpds:products) (lnoop rnoop:products_noop_t)
  (hint:products_hint_t) : bool :=
  match lpds, rpds with
    | nil, nil => true
    | (product_fdef lfdef)::ltl, (product_fdef rfdef)::rtl =>
      let lfname := getFdefID lfdef in
      let rfname := getFdefID rfdef in
      (id_dec lfname rfname)
        && (match lookupAL _ hint lfname with
              | None => false
              | Some hint =>
                valid_fdef lm rm lfdef rfdef 
                (get_noop_by_fname lfname lnoop) (get_noop_by_fname lfname rnoop)
                hint
            end)
        && (valid_products lm rm ltl rtl lnoop rnoop hint)
    | (product_gvar lg)::ltl, (product_gvar rg)::rtl => 
      my_gvar_dec lg rg &&
      valid_products lm rm ltl rtl lnoop rnoop hint
    | (product_fdec (fdec_intro lfh ldk))::ltl, 
      (product_fdec (fdec_intro rfh rdk))::rtl => 
      fheader_dec lfh rfh &&
      deckind_dec rdk ldk &&
      valid_products lm rm ltl rtl lnoop rnoop hint
    | _,_ => false
  end.

Definition valid_module (lmod rmod:module) (lnoop rnoop:module_noop_t) 
  (hint:products_hint_t) : bool :=
  match lmod, rmod with
    | module_intro lly lnd lpds, module_intro rly rnd rpds =>
      layouts_dec lly rly &&
      namedts_dec lnd rnd &&
      valid_products lmod rmod lpds rpds lnoop rnoop hint
  end.

Fixpoint valid_modules (lmods rmods:modules) (lnoop rnoop:modules_noop_t)
  (hint:modules_hint_t) : bool :=
  match lmods, rmods, hint, lnoop, rnoop with
    | nil, nil, nil, nil, nil => true
    | lhd::ltl, rhd::rtl, invhd::invtl, lnhd::lntl, rnhd::rntl =>
      (valid_module lhd rhd lnhd rnhd invhd) &&
      (valid_modules ltl rtl lntl rntl invtl)
    | _, _, _, _, _ => false
  end.

Definition valid_system (lsys rsys:system) (lnoop rnoop:system_noop_t)
  (hint:modules_hint_t) : bool :=
  valid_modules lsys rsys lnoop rnoop hint.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
