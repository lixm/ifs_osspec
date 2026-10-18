
Require Import LibTactics.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import state.
Require Import rules.

Require Import int_auto.
Require Import my_tacs.

Require Import specs_common.
Require Import tick_spec. 
Require Import sys_spec.
Require Import rly_guar.
Require Import flow_policy.
Require Import obsr_equiv.

Require Import aux_lemmas.
Require Import dteq_props.
Require Import tick2_equiv.
Require Import inv_props.

Require Import ver_tick_handler.
Require Import ver_mq_pend.
Require Import ver_mq_post.
Require Import ver_task_create. 
Require Import ver_task_delete.
Require Import ver_chan_recv. 
Require Import ver_chan_send.  

Ltac good_stmts_solver :=
  match goal with
    H: context [if ?t then _ else _] |- _ => 
      destruct t;
      [ 
        try
          match goal with 
            H0: Some _ = Some _ |- _ => inverts H0; try (introv Hf; simpljoin; tryfalse) 
          end
      | idtac]
  end. 

Lemma good_stmts_osspec:  good_stmts (api_spec, int_spec, get_hprio_in_dom). 
Proof.
  unfolds.
  split.
  -
    introv Haf Hmt.
    unfolds in Haf.
    simpl in Haf.
    repeat good_stmts_solver.
    inverts Haf.
  -
    introv His.
    unfolds in His.
    simpl in His.
    destruct i.
    + inverts His. introv Hf; simpljoin; tryfalse.
    + inverts His.
Qed. 

Lemma well_rg_holds:
  well_rg rly_tsk_env guar_tsk_env rly_itp_env guar_itp_env. 
Proof.
  unfolds.
  split.
  - intros.
    split; unfolds; split; intros; auto.
  - intros.
    split.
    +
      introv Hgie.
      split.
      * unfold guar_itp_env in *.
        unfold rly_tsk_env.
        destruct Hgie as (Hsd & Hqd).
        split.
        **
          introv Hsd_.
          eapply Hsd; eauto.
        **
          introv Hqd_.
          eapply Hqd; eauto.
      *
        unfold rly_itp_env. auto.
    +
      introv Hnet Hgte.
      split.
      *
        unfold guar_tsk_env in *.
        unfold rly_tsk_env.
        destruct Hgte as (Hsd & Hqd).
        split; eauto.
      *
        unfolds. auto.
Qed.

Lemma ex_active_tsk_in_dom:
  forall O tls t td, 
    ex_active_tsk O t td ->
    get O abstcblsid = Some (abstcblist tls) ->
    ex_tsk_in_dom t td tls.
Proof.
  introv Hexa Hg.
  unfolds in Hexa.
  simpljoin.
  rewrite H in Hg.
  inverts Hg.
  unfolds.
  do 4 eexists; eauto.
Qed. 

Lemma ex_tsk_in_dom_active_tsk: 
  forall O tls t td, 
    ex_tsk_in_dom t td tls ->
    get O abstcblsid = Some (abstcblist tls) ->
    ex_active_tsk O t td. 
Proof.
  introv Hext Hg.
  unfolds in Hext.
  simpljoin.
  unfolds.
  do 5 eexists.
  splits; eauto.
Qed.   

Lemma ex_free_tsk_in_fts:
  forall O t td fts, 
    ex_free_tsk O t td -> 
    get O freetid = Some (freetidlist fts) ->
    exists ts, get fts td = Some ts /\ In t ts.
Proof.
  introv Heft Hfts.
  unfolds in Heft.
  simpljoin.
  rewrite H in Hfts; inverts Hfts.
  eexists; splits; eauto.
Qed. 

Lemma ex_active_tsk_dteq_impl:
  forall O1 O2 t td, 
    ex_active_tsk O1 t td -> 
    obsr_equiv_tasks td O1 O2 -> 
    ex_active_tsk O2 t td.
Proof.
  introv Heat Hdte.
  assert (Heat_:=Heat).
  unfold ex_active_tsk in *.
  destruct Heat as (tls1 & pr1 & st1 & msg01 & sus1 & Hgtls1 & Hgt1).
  unfolds in Hdte.
  destruct Hdte as (Hnneq & Hall).
  assert (Hex2: exists tls2, get O2 abstcblsid = Some (abstcblist tls2)).
  {
    eapply Hnneq; eauto.
  }
  destruct Hex2 as (tls2 & Hgtls2).
  lets H__: Hall t Hgtls1 Hgtls2; eauto.
  clear Hall.
  lets H_: ex_active_tsk_in_dom Heat_ Hgtls1.
  eapply H__ in H_; eauto.
  unfolds in H_.
  simpljoin.
  do 5 eexists; splits; eauto.
Qed. 

Lemma ex_free_tsk_dteq_impl:
  forall O1 O2 t td, 
    ex_free_tsk O1 t td -> 
    obsr_equiv_freetids td O1 O2 ->
    ex_free_tsk O2 t td. 
Proof.
  introv Heft Hfteq.
  unfold ex_free_tsk in *.
  unfolds in Hfteq.
  destruct Hfteq as (Heqv & Hall).
  simpljoin.
  assert (exists fts, get O2 freetid = Some (freetidlist fts)).
  {
    eapply Heqv; eauto.
  }
  simpljoin.
  lets H__: Hall H H2.
  eapply H__ in H0; eauto.
Qed.

Lemma dteq_sdom_impl:
  forall I O1 O2 td t
         (Hinv1 : I O1)
         (Hinv2 : I O2)
         (Hoe : obsr_equiv_data (TaskDom td) O1 O2)
         (Hsd1: sdom O1 t td),
    sdom O2 t td. 
Proof.
  intros.
  unfold sdom in *.
  unfold state in *. 
  unfold sdom_ in *.

  inverts Hoe.   
  destruct Hsd1 as [Hexa | Hexf].
  -
    left. eapply ex_active_tsk_dteq_impl; eauto.
  -
    right. eapply ex_free_tsk_dteq_impl; eauto.
Qed. 
  
Lemma tsk_same_dom_dteq: tsk_same_dom obsr_equiv_data.
Proof.
  unfolds.
  introv Hinv1 Hinv2 Hoe.
  split.
  - eapply dteq_sdom_impl; eauto.
  - eapply obsr_equiv_data_sym in Hoe.
    introv Hsd.
    lets H__: dteq_sdom_impl Hinv2 Hinv1; eauto.    
Qed.

Lemma good_dteq_dteq: good_dteq obsr_equiv_data.
Proof.
  constructors.
  - intros.
    constructors.
    unfolds.
    + 
      intros. apply obsr_equiv_data_refl.
    +
      unfolds. intros.
      apply obsr_equiv_data_sym; auto.
    +
      unfolds.
      introv Hdte12 Hdte23.
      eapply obsr_equiv_data_trans; eauto.
  -
    apply tsk_same_dom_dteq.
Qed. 

Lemma get_hpr_is_func:
  forall O td t t', 
    get_hprio_in_dom O td t ->
    get_hprio_in_dom O td t' -> 
    t = t'. 
Proof.
  introv Hghpr Hghpr'.
  unfold get_hprio_in_dom in *.
  destruct Hghpr as (tls & pr & m & sus & Hgtls & Hgt & Ha).
  destruct Hghpr' as (tls' & pr' & m' & sus' & Hgtls' & Hgt' & Ha').
  rewrite Hgtls' in Hgtls; inverts Hgtls.
  casetac t t' He Hne.
  - auto.
  - lets H_: Ha (not_eq_sym Hne) Hgt'.
    lets H__: Ha' Hne Hgt.
    eapply Int.ltu_inv in H_; eauto.
    eapply Int.ltu_inv in H__; eauto.
    false.
    auto with zarith.
Qed. 

Lemma sd_is_func_holds: sd_is_func get_hprio_in_dom.
Proof.
  unfolds.
  intros.
  eapply get_hpr_is_func; eauto.
Qed. 

Lemma get_hpr_active_in_dom:
  forall O t td,
    get_hprio_in_dom O td t -> 
    ex_active_tsk O t td. 
Proof. 
  introv Hg.
  unfold get_hprio_in_dom in Hg.
  unfolds.
  simpljoin.
  do 5 eexists; splits; eauto.
Qed. 

Lemma get_hpr_in_dom:
  forall O td t, 
    get_hprio_in_dom O td t -> 
    sdom O t td. 
Proof.
  introv Hghp.
  unfolds. unfold state.
  unfolds.
  left.
  eapply get_hpr_active_in_dom; eauto.
Qed. 

Lemma sched_in_dom_holds: sched_in_dom get_hprio_in_dom.
Proof.
  unfolds. 
  introv Hghp.
  apply get_hpr_in_dom; auto.
Qed.   
 
Lemma ghpr_impl:
  forall O1 O2 td t,
    I O1 ->
    I O2 ->
    obsr_equiv_data (TaskDom td) O1 O2 -> 
    get_hprio_in_dom O1 td t ->
    get_hprio_in_dom O2 td t. 
Proof.
  introv Hinv1 Hinv2 Hdte Hghpr1.
  unfold get_hprio_in_dom in *.
  destruct Hghpr1 as (tls1 & prio1 & msg01 & sus1 & Hgtls1 & Hgt1 & Hall1).
  unfolds in Hdte.
  inverts Hdte.
  unfolds in oe_td_tasks.
  destruct oe_td_tasks as (heqv & Hall).
  assert (Hex2: exists tls, get O2 abstcblsid = Some (abstcblist tls)).
  {
    eapply heqv; eauto.
  }
  destruct Hex2 as (tls2 & Hgtls2).
  lets H__: Hall t Hgtls1 Hgtls2.
  destruct H__ as (Hexeq & Hall_).
  assert (Hex: ex_tsk_in_dom t td tls1).
  {
    unfolds. do 4 eexists; eauto.
  }
  apply Hexeq in Hex.
  unfolds in Hex.
  destruct Hex as (pr2 & st2 & m2 & sus2 & Hgt2).
  lets H__: Hall_ Hgt1 Hgt2.
  specializes H__; eauto.
  destructs H__; subst.
  do 4 eexists; splits.
  eapply Hgtls2. eapply Hgt2.
  introv Hneqt Hgtls2'.
  clear Hall_.
  specialize (Hall tls1 tls2 t').
  specialize (Hall Hgtls1 Hgtls2).
  destruct Hall as (Hex_eq' & Hall').

  assert (Hex: ex_tsk_in_dom t' td tls2).
  { 
    unfolds. do 4 eexists; eauto.
  }
  apply Hex_eq' in Hex.
  unfolds in Hex.
  destruct Hex as (pr1 & st1 & m1 & sus1 & Hgtls1').
  lets H__: Hall' Hgtls1' Hgtls2'.
  specialize (H__ (eq_refl _)).
  destructs H__; subst.
  
  eapply Hall1; eauto.
Qed.   

Lemma sched_same_choice_holds:
  sched_same_choice get_hprio_in_dom obsr_equiv_data.
Proof.
  unfolds.
  introv Hinv1 Hinv2 Hdteq.
  intros.
  split; introv Hghpr.
  - 
    lets H__: ghpr_impl Hinv1 Hinv2; auto.
  -
    apply obsr_equiv_data_sym in Hdteq.
    eapply ghpr_impl; eauto.
Qed.   

Lemma uct_dteq_tasks:
  forall O cid t O' td, 
    upd_cur_tsk O cid t O' -> 
    obsr_equiv_tasks td O O'. 
Proof.
  introv Huct.
  unfolds in Huct.
  unfold state in Huct.
  unfolds in Huct.
  destruct Huct as (ct & ct' & Hgct & Hct' & HO').
  unfolds.
  rewrite HO'.
  rewrite neq_set_get; eauto.
  2: { introv Hf. inverts Hf. }
  split.
  - split; intro; auto.
  - introv Hgtls1 Hgtls2.
    rewrite Hgtls1 in Hgtls2; inverts Hgtls2.
    split.
    + split; intro; auto.
    + introv Hg1 Hg2.
      rewrite Hg1 in Hg2.
      inverts Hg2.
      intro.
      splits; eauto.
Qed. 

Lemma uct_dteq_mqs:
  forall O cid t O' td, 
    upd_cur_tsk O cid t O' -> 
    obsr_equiv_mqs td O O'. 
Proof.
  introv Huct.
  unfolds in Huct.
  unfold state in Huct.
  unfolds in Huct.
  destruct Huct as (ct & ct' & Hgct & Hct' & HO').
  unfolds. 
  rewrite HO'.
  rewrite neq_set_get; eauto.
  2: { introv Hf. inverts Hf. }
  split.
  - split; intro; auto.
  - introv Hgqls1 Hgqls2.
    rewrite Hgqls1 in Hgqls2; inverts Hgqls2.
    split.
    + split; intro; auto.
    + introv Hg1 Hg2.
      rewrite Hg1 in Hg2.
      inverts Hg2.
      intro.
      auto.
Qed. 

Lemma uct_dteq_chans:
  forall O cid t O' td, 
    upd_cur_tsk O cid t O' -> 
    obsr_equiv_chans td O O'. 
Proof.
  introv Huct.
  unfolds in Huct.
  unfold state in Huct.
  unfolds in Huct.
  destruct Huct as (ct & ct' & Hgct & Hct' & HO').
  unfolds. 
  rewrite HO'.
  rewrite neq_set_get; eauto.
  2: { introv Hf. inverts Hf. }
  split.
  - split; intro; auto.
  - introv Hgcls1 Hgcls2.
    rewrite Hgcls1 in Hgcls2; inverts Hgcls2.
    split.
    + split; intro; auto.
    + introv Hg1 Hg2.
      rewrite Hg1 in Hg2.
      inverts Hg2.
      split.
      * tauto.
      * intros. split; auto.
Qed. 

Lemma uct_dteq_fts:
  forall O cid t O' td, 
    upd_cur_tsk O cid t O' -> 
    obsr_equiv_freetids td O O'. 
Proof.
  introv Huct.
  unfolds in Huct.
  destruct Huct as (ct & ct' & Hgct & Hct' & HO').
  unfolds. 
  rewrite HO'.
  rewrite neq_set_get; eauto.
  2: { introv Hf; inverts Hf. }
  split.
  - split; intro; auto.
  - introv Hgcls1 Hgcls2.
    rewrite Hgcls1 in Hgcls2; inverts Hgcls2.
    tauto.
Qed. 

Lemma uct_dteq_fqs:
  forall O cid t O' td, 
    upd_cur_tsk O cid t O' -> 
    obsr_equiv_freeqids td O O'. 
Proof.
  introv Huct.
  unfolds in Huct.
  destruct Huct as (ct & ct' & Hgct & Hct' & HO').
  unfolds. 
  rewrite HO'.
  rewrite neq_set_get; eauto.
  2: { introv Hf; inverts Hf. }
  split.
  - split; intro; auto.
  - introv Hgcls1 Hgcls2.
    rewrite Hgcls1 in Hgcls2; inverts Hgcls2.
    tauto.
Qed. 

Lemma uct_sch_eq: 
  forall O cid t O', 
    upd_cur_tsk O cid t O' -> 
    obsr_equiv_schd O O'. 
Proof.
  introv Huct.
  unfolds in Huct.
  destruct Huct as (ct & ct' & Hgct & Hct' & HO').
  constructors; 
    try (
        subst O'; 
        rewrite neq_set_get; eauto; 
        introv Hf; inverts Hf
      ).
Qed. 

Lemma swi_dteq_holds: swi_dteq obsr_equiv_data.
Proof.
  unfolds.
  introv Huct.
  unfolds.
  destruct d.
  -
    constructors.
    +
      eapply uct_dteq_tasks; eauto.
    +
      eapply uct_dteq_mqs; eauto.
    +
      eapply uct_dteq_chans; eauto.
    +
      eapply uct_dteq_fts; eauto.
    +
      eapply uct_dteq_fqs; eauto.
  -
    eapply uct_sch_eq; eauto.
Qed. 

Lemma sched_same_dom_holds:
  sched_same_dom get_hprio_in_dom. 
Proof.
  unfolds.
  introv Hinv Hcd Hghpr Huct.
  intros.
  eapply uct_tsks_same_dom; eauto.
Qed.   

Ltac func_no_tick0 :=
  match goal with
  | H: _ \/ _ |- _ => try destruct H
  | H: exists _, _ |- _ => simpljoin
  | H: _ /\ _ |- _ => simpljoin
  | H: context[task_apispecs.taskcre_tcb_alloc] |- _ => unfolds in H
  | H: context[task_apispecs.task_del_tcb_release] |- _ => unfolds in H
  (* | H: context[mq_apispecs.qcre_prim] |- _ => unfolds in H *)
  | H: context[chan_apispecs.chpend_prim] |- _ => unfolds in H
  | H: context[chan_apispecs.chpost_prim] |- _ => unfolds in H
  | H: context [match ?t with _ => _ end] |- _ => 
      destruct t
  | H: context [has_tick'] |- _ =>
      simpl in H                   
  | H: context [if ?t then _ else _] |- _ =>
      destruct t
  | H: context [err_prop] |- _ => try (inverts H; simpljoin; tryfalse)
  | H: context [spec_skip_step] |- _ => unfold spec_skip_step in H
  | _ => tryfalse
  end.

Definition q_star := fun (_ : tid) (_ : vallist) (_ : osabst) => True. 
                                                         
Lemma no_tick_in_kfunc_holds: no_tick_in_kfunc api_spec. 
Proof.
  unfolds.
  introv Haf Htck.
  unfolds in Haf.
  simpl in Haf.

  destruct (Zeq_bool OSTaskCreate f).
  inverts Haf.                                            
  repeat func_no_tick0.

  destruct (Zeq_bool OSTaskDel f).
  inverts Haf. 
  repeat func_no_tick0.
  
  destruct (Zeq_bool OSQPend f). 
  inverts Haf.
  repeat func_no_tick0.

  destruct (Zeq_bool OSQPost f). 
  inverts Haf.
  repeat func_no_tick0.

  destruct (Zeq_bool OSChanRecv f).
  inverts Haf.
  repeat func_no_tick0. 

  destruct (Zeq_bool OSChanSend f).
  inverts Haf.
  repeat func_no_tick0.

  false. 
Qed.   


Lemma tick_dt_equiv_holds: tick_dt_equiv int_spec obsr_equiv_data. 
Proof.
  unfolds.
  introv Hinv1 Hinv2 Hoesch Hoed Htck1 Htck2.
  unfold int_spec in *.
  unfold has_tick in *.
  destruct Htck1 as (i1 & s1 & Hs1 & Htck1).
  destruct Htck2 as (i2 & s2 & Hs2 & Htck2).
  simpl in Hs1.
  simpl in Hs2.
  destruct i1; destruct i2; simpl in Hs1, Hs2; tryfalse.
  inverts Hs1; inverts Hs2.
  destruct d.
  -
    unfold obsr_equiv_data.
    eapply tck_dte_holds; eauto.
  -
    lets H_: tck_dte_sch_holds Hinv1 Hinv2; eauto.
Qed. 

Lemma tick_cdom_eq_holds: tick_cdom_eq int_spec obsr_equiv_data. 
Proof.
  unfolds.
  introv Hinv1 Hinv2 Hoesch Htck1 Htck2.
  unfold int_spec in *.
  unfold has_tick in *.
  destruct Htck1 as (i1 & s1 & Hs1 & Htck1).
  destruct Htck2 as (i2 & s2 & Hs2 & Htck2).
  simpl in Hs1.
  simpl in Hs2.
  destruct i1; destruct i2; simpl in Hs1, Hs2; tryfalse.
  inverts Hs1; inverts Hs2.
  intros td.
  
  lets H_: tck_oe_sch_cdomeq Hinv1 Hinv2; eauto.
Qed.  

Lemma tck_diff_cid_cdom_eq:
  forall O O' t cid vl cid'
         (Hinv : I O)
         (Htck : has_tick' tickisr t cid O vl O')
         (Hneq : cid <> cid'), 
  forall td : task_dom, get_cur_dom O cid' td <-> get_cur_dom O' cid' td. 
Proof.
  intros.
  unfold tickisr, has_tick' in *.
  destruct Htck; simpljoin; tryfalse. 
  2: { destruct H; simpljoin; tryfalse. }
    
  unfold tickisr_spec in *.
  
  destruct H as (tls & qls & ctid & dtmp & dt & cdmp & cd & cid_ & Hgct &
                   Hgt & Hgtls & Hgqls & Hgdtmp & Hgdt & Hact & Hgcmp & Hgcd & Hex).
  
  destruct Hex as (tls' & qls' & Hstep & Hif).
  assert (cid = cid_) by congruence.
  subst cid_.
  
  d_if_hyp.
  
  - (* case where current domain changes *)

    destruct Hif as (imp & lmp & ldmp & scdmp & idx & len & ld & schd & H'). 
    destruct H' as (Hgimp & Hgidx & Hglmp & Hglen & Hgldmp &
                      Hgld & Hgscdmp & Hgschd & H'). 
    
    d_mt_hyp.
    + 
      destruct p. 
      destruct H' as (HO' & Hvl').
      subst O'. 
      unfold get_cur_dom.
      rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
      rewrite map_get_set.
      split.
      * introv Hex.
        simpljoin.
        eexists; splits; eauto.
        rewrite neq_set_get; eauto.
        rewrite Hact in H.
        inverts H.
        auto.
      * introv Hex.
        simpljoin.
        inverts H.
        rewrite neq_set_get in H0; eauto.
    +
      destruct H' as (HO' & Hvl').
      subst.
      tauto.

  - (* case where current domain does not change *)

    destruct Hif.
    subst O'.
    unfold get_cur_dom.
    repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    tauto.
Qed. 


Lemma tick_prsv_cdom_holds:
  tick_preserves_cdom int_spec obsr_equiv_data. 
Proof.
  unfolds.
  introv Hinv Htck Hneq.
  unfold int_spec in *.
  unfold has_tick in *.
  destruct Htck as (i & s & Hs & Htck).
  simpl in Hs.
  destruct i; simpl in Hs; tryfalse. 
  inverts Hs.
  unfold cur_dom.
  unfold state.
  eapply tck_diff_cid_cdom_eq; eauto.
Qed.   
  
Lemma sched_inv_holds: sched_inv get_hprio_in_dom.
Proof.
  unfolds.
  introv Hinv Hcd Hgh Hu.
  eapply inv_ct_change_prsv; eauto.
Qed.
  
Require Import soundness. 

Theorem top_rule_holds:
  top_rule rly_tsk_env guar_tsk_env rly_itp_env guar_itp_env flows_to obsr_equiv_data krnl_spec.
Proof.
  unfold krnl_spec.  
  constructors; eauto.
  - apply good_stmts_osspec.
  - apply well_rg_holds.
  - constructors.
    + (* tick_dt_equiv *)
      apply tick_dt_equiv_holds.
    (* + (* tick_output_eq *) *)
    (*   apply tick_output_eq_holds. *)
    + (* no_tick_in_kfunc *) 
      apply no_tick_in_kfunc_holds.
    + (* tick_cdom_eq *)
      apply tick_cdom_eq_holds. 
    + (* tick_preserves_cdom *)
      apply tick_prsv_cdom_holds.
    + (* sched_inv *)
      apply sched_inv_holds. 
    + (* sched_same_dom *)
      eapply sched_same_dom_holds; eauto.
    + (* swi_dteq *)
      apply swi_dteq_holds.
    + (* sched_same_choice *)
      apply sched_same_choice_holds.
    + (* sched_in_dom *)
      apply sched_in_dom_holds.
    + (* sd_is_func *) 
      apply sd_is_func_holds.
  - apply good_dteq_dteq. 
  -
    introv Haf Htvm.
    unfolds in Haf.
    simpl in Haf.
    d_if_hyp.
    inverts Haf.
    { (* OSTaskCreate *) 
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star.
          eapply dr_taskcre; eauto.
    }
    d_if_hyp.
    inverts Haf.
    { (* OSTaskDel *) 
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star.
          eapply dr_taskdel; eauto.
    }
    d_if_hyp.
    inverts Haf.
    { (* OSQPend *)
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star.
          eapply dr_qpend; eauto.
    }
    d_if_hyp.
    inverts Haf.
    { (* OSQPost *)
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star.
          eapply dr_qpost; eauto.
    }
    d_if_hyp.
    inverts Haf.    
    { (* OSChanRecv *)
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star. 
          eapply dr_chanrecv; eauto.
    }
    d_if_hyp.
    inverts Haf.    
    { (* OSChanSend *)
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star.
          eapply dr_chansend; eauto.
    }      
    false. 
  -
    introv Hispc.
    unfolds in Hispc.
    simpl in Hispc.
    destruct i.
    inverts Hispc.
    { (* Tick ISR *)
      -
        split.
        + 
          introv Hinv.
          simpl; unfolds; auto.
        +
          exists q_star.
          eapply dr_tick_handler; eauto.
    }
    false. 
    
Qed. 

Require Import properties. 
Require Import soundness.

Theorem sys_sec:
  forall (init: sys_config_t -> Prop) uprgs,
    good_init init -> 
    (confidentiality_u flows_to uprgs krnl_spec init obsr_equiv_data /\
       integrity_u flows_to uprgs krnl_spec init obsr_equiv_data). 
Proof. 
  introv Hgini.
  pose proof top_rule_holds as Htr.
  assert (good_flt flows_to).
  {
    unfolds.
    splits; try constructors.
    introv Hfl.
    inverts Hfl; auto.
  }
  split.
  -
    eapply soundness_confidentiality; eauto.
  -
    eapply soundness_integrity; eauto.
Qed. 

