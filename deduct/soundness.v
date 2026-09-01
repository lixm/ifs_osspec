
Require Import LibTactics.
Require Import memory.
Require Import language. 
Require Import opsem.
Require Import rules.
Require Import properties.
Require Import my_tacs.
Require Import map_tactics.
Require Import rch_lemmas.
Require Import inversion_lemmas. 

Require Import Coq.Classes.RelationClasses.

Section Soundness.

Context {state_t : Type}.  
Context `{State state_t}.

Definition tsks_exe_strat (T: tasks) :=
  forall t C, T t = Some C -> exists strat, C = (cur_strat strat, kstop). 

Definition good_init (init: sys_config_t -> Prop) :=
  init cfg0 -> (tsks_exe_strat (fst (fst cfg0)) /\ I (snd cfg0)).

Definition good_flt (flt: flows_to_t) :=
  (forall d, flt d d) /\
    (forall d, flt SchedDom d) /\
    (forall d, flt d SchedDom -> d = SchedDom).

Lemma prog_equiv_refl:
  forall td T O, prog_equiv td T T O O.
Proof. 
  intros.
  unfolds.
  intros.
  auto.
Qed.

Lemma ust_equiv_refl:
  forall i ust,
    ust_equiv i ust ust.
Proof.
  intros.
  unfolds.
  auto.
Qed. 

Lemma same_cdom_refl:
  forall O,
    same_cdom O O.
Proof.
  intros. unfolds. intros.
  split; auto.
Qed. 

Lemma same_td_for_ct_refl:
  forall O, 
    I O -> same_td_for_ct O O.
Proof.
  intros.
  unfolds.
  split.
  -
    split; auto.
  -
    introv Hct1 Hct2.
    intros.
    lets H__: cur_tsk_is_fn Hct1 Hct2; eauto.
    subst.
    split; auto.
Qed. 

Lemma same_td_for_ct_sym:
  forall O1 O2, 
    same_td_for_ct O1 O2 -> 
    same_td_for_ct O2 O1. 
Proof.
  intros O1 O2 Hsame.
  unfold same_td_for_ct in *.

  intros.
  destruct (Hsame cid) as (Heqv & Hsd). clear Hsame.
  split. 
  -
    symmetry. auto.
  -
    introv Hct1 Hct2.
    lets H_: Hsd Hct2 Hct1; eauto.
    intros.
    specialize (H_ td).
    symmetry.  
    auto.
Qed.  

Lemma same_td_for_ct_trans:
  forall O1 O2 O3, 
    same_td_for_ct O1 O2 ->
    same_td_for_ct O2 O3 ->
    same_td_for_ct O1 O3.
Proof.
  intros O1 O2 O3 H12 H23.
  unfold same_td_for_ct in *.
  intro cid.
  split.
  - (* existence equivalence *)
    split.
    + intros [t1 Hcur1].
      destruct (H12 cid) as [Hex12 _].
      destruct (H23 cid) as [Hex23 _].
      apply Hex23.
      apply Hex12.
      exists t1.
      assumption.
    + intros [t3 Hcur3].
      destruct (H23 cid) as [Hex23 _].
      destruct (H12 cid) as [Hex12 _].
      apply Hex12.
      apply Hex23.
      exists t3.
      assumption.

  - (* sdom equivalence *)
    intros t1 t3 Hcur1 Hcur3 td.
    destruct (H12 cid) as [_ Hs12].
    destruct (H23 cid) as [_ Hs23].

    (* Find the corresponding task in O2 from the first relation *)
    assert (exists t2, cur_tsk O2 cid t2) as Hex2.
    {
      apply (proj1 (H12 cid)).
      exists t1.
      assumption.
    }
    destruct Hex2 as [t2 Hcur2].

    specialize (Hs12 t1 t2 Hcur1 Hcur2 td).
    specialize (Hs23 t2 t3 Hcur2 Hcur3 td).

    split.
    + intros.
      apply (proj1 Hs23).
      apply (proj1 Hs12).
      assumption.
    + intros. 
      apply (proj2 Hs12).
      apply (proj2 Hs23).
      assumption.
Qed.

Lemma ctid_equiv_refl:
  forall td O, I O -> ctid_equiv td O O.
Proof.
  intros.
  unfolds.
  introv Hct1 Hct2 Hsd.
  lets H_: cur_tsk_is_fn Hct1 Hct2; eauto.
Qed.   

Lemma ctid_equiv_sym_scd:
  forall td O1 O2,
    same_td_for_ct O1 O2 -> 
    ctid_equiv td O1 O2 ->
    ctid_equiv td O2 O1. 
Proof.
  introv Hscd Hce.
  unfold ctid_equiv in *.
  introv Hgct1 Hgct2 Hsd.
  lets H__: Hce Hgct2 Hgct1.
  symmetry; apply H__; eauto.
  clear H__.
  unfolds in Hscd.
  simpljoin.
  specialize (Hscd cid).
  destruct Hscd as (Heqv & Hall).
  lets H__: Hall Hgct2 Hgct1; eauto.
  eapply H__; eauto.
Qed. 

Lemma ctid_equiv_trans_scd:
  forall td O1 O2 O3,
    same_td_for_ct O1 O2 ->  
    ctid_equiv td O1 O2 ->
    ctid_equiv td O2 O3 ->
    ctid_equiv td O1 O3.  
Proof.
  introv Hscd12 (* Hscd23 *) Hce12 Hce23.
  unfold ctid_equiv in *.
  introv Hgct1 Hgct3.
  rename t2 into t3.
  introv Hsd.
  assert (Hsd_ := Hsd).
  unfolds in Hscd12.
  specialize (Hscd12 cid).
  destruct Hscd12 as (Heqv & Hall12).
  assert (Hex: exists t, cur_tsk O1 cid t).
  { eexists; eauto. }
  apply Heqv in Hex.
  destruct Hex as (t2 & Hgct2).
  specialize (Hall12 _ _ Hgct1 Hgct2).
  eapply Hall12 in Hsd; eauto.
  specialize (Hce23 cid _ _ Hgct2 Hgct3).
  specializes Hce23; eauto.
  specialize (Hce12 cid _ _ Hgct1 Hgct2).
  specializes Hce12; eauto.
  congruence. 
Qed. 

Lemma prog_equiv_sym:
  forall td T1 T2 O1 O2, 
    prog_equiv td T1 T2 O1 O2 ->
    prog_equiv td T2 T1 O2 O1.
Proof.
  introv H12.
  unfold prog_equiv in *.
  introv Hsd2 Hsd1.
  symmetry.
  eapply H12; eauto.
Qed.

Lemma prog_equiv_trans:
  forall td T1 T2 T3 O1 O2 O3, 
    (forall t, sdom O1 t td <-> sdom O2 t td) -> 
    prog_equiv td T1 T2 O1 O2 ->
    prog_equiv td T2 T3 O2 O3 ->
    prog_equiv td T1 T3 O1 O3.
Proof.
  introv Hsdeq Hpe12 Hpe23.
  unfold prog_equiv in *.
  introv Hsd1 Hsd3.
  assert (Hsd2: sdom O2 t td).
  { eapply Hsdeq; eauto. }
  specializes Hpe12; eauto.
  specializes Hpe23; eauto.
  congruence.
Qed.

Lemma ust_equiv_sym:
  forall td ust1 ust2, 
    ust_equiv td ust1 ust2 ->
    ust_equiv td ust2 ust1. 
Proof.
  introv Hue.
  unfold ust_equiv in *.
  eauto.
Qed.

Lemma ust_equiv_trans:
  forall td ust1 ust2 ust3, 
    ust_equiv td ust1 ust2 ->
    ust_equiv td ust2 ust3 ->
    ust_equiv td ust1 ust3.
Proof.
  introv H12 H23.
  unfold ust_equiv in *.
  congruence. 
Qed.

Lemma same_cdom_sym:
  forall O1 O2, 
    same_cdom O1 O2 -> 
    same_cdom O2 O1. 
Proof.
  introv Hsc12.
  unfold same_cdom in *.
  intros.
  specialize (Hsc12 cid td).
  symmetry.
  auto.
Qed. 

Lemma same_cdom_trans: 
  forall O1 O2 O3, 
    same_cdom O1 O2 -> 
    same_cdom O2 O3 ->
    same_cdom O1 O3. 
Proof.
  introv Hsc12 Hsc23.
  unfold same_cdom in *.
  intros.
  specialize (Hsc12 cid td).
  specialize (Hsc23 cid td).
  rewrite Hsc12.
  auto.
Qed. 

Lemma obsr_equiv_sym:
  forall T1 ust1 O1 T2 ust2 O2 d dteq, 
    good_dteq dteq -> 
    same_td_for_ct O1 O2 -> 
    obsr_equiv d dteq (T1, ust1, O1) (T2, ust2, O2) ->
    obsr_equiv d dteq (T2, ust2, O2) (T1, ust1, O1). 
Proof.
  introv Hgd Hstfc12 Hoe12.
  unfold obsr_equiv in *.
  destruct Hoe12 as (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ & Heq1 & Heq2 & Hmt).
  symmetry in Heq1.
  symmetry in Heq2.
  inverts Heq1.
  inverts Heq2.
  do 6 eexists; splits; eauto.
  destruct d.
  -
    destructs Hmt; splits.
    + 
      eapply prog_equiv_sym; eauto.
    +
      eapply ust_equiv_sym; eauto.
    +
      eapply ctid_equiv_sym_scd; eauto.
    +
      inverts Hgd.
      specialize (gd_equiv_rel (TaskDom i)).
      inverts gd_equiv_rel.
      eapply Equivalence_Symmetric; eauto.
  -
    destructs Hmt; splits.
    +
      eapply same_cdom_sym; eauto.
    +
      eapply same_td_for_ct_sym; eauto.
    +
      inverts Hgd.
      specialize (gd_equiv_rel SchedDom).
      inverts gd_equiv_rel.
      eapply Equivalence_Symmetric; eauto.
Qed. 

Lemma obsr_equiv_trans:
  forall T1 ust1 O1 T2 ust2 O2 T3 ust3 O3 d dteq,  
    I O1 -> I O2 -> 
    good_dteq dteq -> 
    same_td_for_ct O1 O2 -> 
    obsr_equiv d dteq (T1, ust1, O1) (T2, ust2, O2) ->
    obsr_equiv d dteq (T2, ust2, O2) (T3, ust3, O3) ->
    obsr_equiv d dteq (T1, ust1, O1) (T3, ust3, O3). 
Proof.
  introv Hinv1 Hinv2 Hgd Hstfc Hoe12 Hoe23.
  inverts Hgd. 
  unfold obsr_equiv in *.
  destruct Hoe12 as (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ & Heq12 & Heq12' & Hmt12).
  symmetry in Heq12; symmetry in Heq12'.
  inverts Heq12; inverts Heq12'.
  destruct Hoe23 as (T2_ & ust2_ & O2_ & T3_ & ust3_ & O3_ & Heq23 & Heq23' & Hmt23).
  symmetry in Heq23; symmetry in Heq23'.
  inverts Heq23; inverts Heq23'.
  do 6 eexists; splits; eauto.
  destruct d.
  -
    simpljoin; splits.
    +
      eapply prog_equiv_trans; eauto.
    +
      eapply ust_equiv_trans; eauto.
    +
      eapply ctid_equiv_trans_scd; eauto.
    +
      specialize (gd_equiv_rel (TaskDom i)).
      inverts gd_equiv_rel.
      eapply Equivalence_Transitive; eauto.
  -
    simpljoin; splits.
    +
      eapply same_cdom_trans; eauto.
    +
      eapply same_td_for_ct_trans; eauto.
    +
      specialize (gd_equiv_rel SchedDom).
      inverts gd_equiv_rel.
      eapply Equivalence_Transitive; eauto.
Qed. 
    
Lemma inv_good_ctrl_hpstepstar_preserved:
  forall sd uprg kspc aspc ispc cfg cfg' rly_tsk guar_tsk rly_itp guar_itp flt dteq, 
    kspc = (aspc, ispc, sd) -> 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprg*) kspc -> 
    hpstep_star uprg kspc cfg cfg' ->
    forall T ust O T' ust' O', 
      cfg = (T, ust, O) ->    
      I O -> 
      (forall t C,
          T t = Some C ->
          good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O C) ->     
      cfg' = (T', ust', O') -> 
      (I O' /\
         (forall t C,
             T' t = Some C -> 
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O' C)).  
Proof. 
  introv Hkspc Htr Hsteps.
  induction Hsteps; introv Hcfg Hinv Hgctrl Hcfg'.
  - 
    subst cfg. inverts Hcfg'.
    split; auto.
  -
    rewrite H0 in Hcfg; inverts Hcfg.
    destruct act.
    lets H_: good_ctrl_sys_step_preserved Htr Hkspc Hinv Hgctrl H2.
    destruct H_ as (Hinv' & Hall').
    lets H_ : IHHsteps Hkspc Htr.
    clear IHHsteps.
    lets H__: H_ H1 Hinv' Hall' Hcfg'.
    auto.
Qed.

Lemma rch_good_ctrl:
  forall rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs kspc aspc ispc sd init cfg T ust O, 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) kspc ->
    kspc = (aspc, ispc, sd) ->
    good_init init -> 
    reachable uprgs kspc init cfg ->  
    cfg = (T, ust, O) -> 
    I O /\ 
      (forall t C, T t = Some C -> good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O C).  
Proof.
  introv Htr Hkspc Hgini Hrc Hcfg.
  unfold reachable in Hrc.
  destruct Hrc as (Hinit & Hsteps).
  lets H_: Hgini Hinit.
  destruct H_ as (Hstrat & (* Hctcore & *) Hinv).
  destruct cfg0 as [[T0 ust0] O0].
  simpl in Hstrat.
  lets H__: inv_good_ctrl_hpstepstar_preserved Hkspc Htr Hsteps.
  eapply H__; eauto.
  clear H__.
  unfolds in Hstrat.
  introv Hget.
  lets H__: Hstrat Hget.
  destruct H__ as (strat & HC).
  subst C.
  simpl.
  auto.
Qed. 


Lemma ctrl_succ_eq_hpstepstar_preserved:
  forall sd uprg kspc aspc ispc cfg cfg', 
    kspc = (aspc, ispc, sd) -> 
    hpstep_star uprg kspc cfg cfg' ->
    forall T ust O T' ust' O', 
      cfg = (T, ust, O) -> 
      (forall t C, T t = Some C -> ctrl_succ_eq aspc ispc C) ->
      cfg' = (T', ust', O') -> 
      (forall t C, T' t = Some C -> ctrl_succ_eq aspc ispc C).
Proof.
  introv Hkspc Hstep.
  induction Hstep; introv Hcfg Hall Hcfg'.
  - 
    subst cfg. inverts Hcfg'.
    auto.
  -
    introv Hget'.
    destruct act.
    subst cfg. inverts Hcfg.
    lets H_: ctrl_succ_eq_sys_step_preserved Hkspc Hall; eauto.
Qed. 

Lemma rch_succ_eq:
  forall uprgs kspc aspc ispc sd init cfg T ust O, 
    kspc = (aspc, ispc, sd) ->
    good_init init -> 
    reachable uprgs kspc init cfg ->  
    cfg = (T, ust, O) -> 
    (forall t C, T t = Some C -> ctrl_succ_eq aspc ispc C). 
Proof.
  introv Hkspc Hgi Hrc Hcfg.
  unfolds in Hrc.
  destruct Hrc as (Hini & Hsteps).
  eapply Hgi in Hini.
  destruct Hini as (Htes & (* Hcc & *) Hinv).
  destruct cfg0 as [[T0 ust0] O0].
  lets H_: ctrl_succ_eq_hpstepstar_preserved Hkspc Hsteps; eauto.
  eapply H_; eauto.
  clear H_.
  simpl in Htes.
  unfolds in Htes.
  introv Hget.
  eapply Htes in Hget; eauto.
  destruct Hget.
  subst C.
  simpl. auto.
Qed.   


Lemma has_tick'_has_tick:
  forall aspc ispc sd s s' ks t cid O O', 
    ctrl_succ_eq aspc ispc (cur_stmt s, ks) -> 
    no_tick_in_kfunc aspc -> 
    spec_step sd t s O s' O' (_TickAct cid) ->                 
    exists vl', has_tick ispc t cid O vl' O'. 
Proof.
  introv Hcse Hntik Hstep.
  unfold ctrl_succ_eq in Hcse.
  destruct Hcse as (Hsse & Hcse).
  destruct Hsse as [Hase | Hise].
  -
    unfolds in Hntik.
    destruct Hase as (f & ac & ft & vl & Hgetf & Hse).
    lets H_: succ_eq_has_tick' Hse Hstep.
    destruct H_ as (vl'_ & Htck').
    unfold no_tick_in_kfunc in Hntik.
    eapply Hntik in Htck'; eauto.
    false.
  -
    destruct Hise as (i_ & s0 & Hgeti & Hse).
    lets H_: succ_eq_has_tick' Hse Hstep.
    destruct H_ as (vl'_ & Htck').
    exists vl'_.
    unfolds.
    do 2 eexists; splits; eauto.
Qed.    

Lemma sdom_tsks_spec_step_preserved:
  forall t (* aspc ispc *) sd rly guar flt dteq s q, 
    (* well_sched aspc ispc sd I dteq sdom -> *)
    deduct_rules t rly guar flt dteq s q -> 
    forall O, 
      I O -> 
      head_sat t O s ->
      forall s' O' ac,  
        spec_step sd t s O s' O' ac ->
        (forall t td, sdom O t td <-> sdom O' t td). 
Proof.
  introv Hdr.
  induction Hdr; introv Hinv Hssp Hstep.
  - 
    simpl in Hssp.
    assert (Hpre: pre1 t O p).
    { unfolds; splits; eauto. }
    inverts Hstep.
    specializes H1; eauto.
    simpljoin; auto.
  -
    inverts Hstep; eapply IHHdr; eauto.
  -
    inverts Hstep.
    intros. split; intro; auto.
  -
    inverts Hstep.
    intros. split; intro; auto.
  -
    inverts Hstep.
Qed. 

Lemma good_stmt_spec_step_same_dom:
  forall t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks s' O' ac, 
    good_stmt t rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks ->
    I O -> 
    spec_step sd t s O s' O' ac ->
    (forall t td, sdom O t td <-> sdom O' t td). 
Proof.
  introv Hgs Hinv Hsstp.
  inverts Hgs.
  destruct H1 as (q & Hor).
  destruct Hor as [(Hhi & Hdr) | (Hnhi & Hdr)];
    eapply sdom_tsks_spec_step_preserved; eauto.
Qed. 

Lemma ct_spec_step_preserved:
  forall sd t s O s' O' ac, 
    spec_step sd t s O s' O' ac ->
    (forall cid t, cur_tsk O cid t <-> cur_tsk O' cid t).   
  (* get O coretid = get O' coretid.  *)
Proof.
  introv Hssp.
  induction Hssp; auto; try (intros; split; auto).
Qed.


Lemma spec_step_head_step_tick:
  forall sd t s O s' O' cid ks aspc ispc, 
    spec_step sd t s O s' O' (_TickAct cid) ->
    ctrl_succ_eq aspc ispc (cur_stmt s, ks) -> 
    no_tick_in_kfunc aspc -> 
    exists step vl,
      head_step s step vl /\
        forall vl' O O', step t vl O (_TickAct cid) (vl', O') -> has_tick ispc t cid O vl' O'.
Proof.
  introv Hstep Hcse Hntik. 
  unfold ctrl_succ_eq in Hcse.
  destruct Hcse as (Hsse & Hcse).
  destruct Hsse as [Hase | Hise].
  -
    unfolds in Hntik.
    destruct Hase as (f & ac & ft & vl & Hgetf & Hse).
    lets H_: succ_eq_has_tick'_vl' Hstep Hse. 
    destruct H_ as (step & vl_ & Hhs & Hall).
    do 2 eexists; splits; eauto.
    introv Hstep_.
    eapply Hall in Hstep_; eauto.
    eapply Hntik in Hstep_; eauto.
    false.
  -
    destruct Hise as (i_ & s0 & Hgeti & Hse).
    lets H_: succ_eq_has_tick'_vl' Hstep Hse.
    destruct H_ as (step & vl_ & Hhs & Hall).
    do 2 eexists; splits; eauto.
    introv Hstep_.
    eapply Hall in Hstep_; eauto.
    unfolds. do 2 eexists; splits; eauto.
Qed.

Lemma same_cur_dom_t1t2_td:
  forall O1 O2 t1 t2 cid,
    same_td_for_ct O1 O2 ->
    cur_tsk O1 cid t1 -> 
    cur_tsk O2 cid t2 -> 
    (forall td, sdom O1 t1 td <-> sdom O2 t2 td). 
Proof.
  introv Hsame_curd Hvc1 Hvc2.
  unfolds in Hsame_curd.
  specialize (Hsame_curd cid).
  destruct Hsame_curd as (Heqv & Hall).
  specialize (Hall _ _ Hvc1 Hvc2).
  auto.
Qed. 

Lemma ticks_preserve_dteq_task_dom: 
  forall rly_tsk guar_tsk rly_itp guar_itp flt (dteq: dt_obeq_t) uprgs aspc ispc sd O1 O2 O1' O2' i 
         T1 T2 T1' T2' ust1 ust2 ust1' ust2' d1' d2' cid
         (Htr: top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd))
         (* (Hsame_cd: same_cdom O1 O2) *)
         (Hsame_curd : same_td_for_ct O1 O2)
         (Hdteq_sch : dteq SchedDom O1 O2)
         (Hoe_d : obsr_equiv (TaskDom i) dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hstep1 : hpstep_d uprgs (aspc, ispc, sd) (T1, ust1, O1) 
                     (T1', ust1', O1') (TickAct cid) d1')
         (Hstep2 : hpstep_d uprgs (aspc, ispc, sd) (T2, ust2, O2) 
                     (T2', ust2', O2') (TickAct cid) d2')
         (Hinv1 : I O1)
         (Hsuc1 : forall (t : tid) (C : code), T1 t = Some C -> ctrl_succ_eq aspc ispc C)
         (Hinv2 : I O2)
         (Hsuc2 : forall (t : tid) (C : code), T2 t = Some C -> ctrl_succ_eq aspc ispc C)
         (Hgctrl1 : forall (t : tid) (C : code),
             T1 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 C)
         (Hgctrl2 : forall (t : tid) (C : code),
             T2 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 C)
         (Hflt : flt d1' (TaskDom i)), 

    prog_equiv i T1' T2' O1' O2' /\
      ust_equiv i ust1' ust2' /\
      ctid_equiv i O1' O2' /\
      dteq (TaskDom i) O1' O2'.  
Proof.
  intros.
  lets H1_: hpstep_d_tick_inversion Hstep1; eauto.
  destruct H1_ as (t1 & ks1 & s1 & s1' & Hvc1 & Hsstp1 & Hget1 & Hset1 & Husteq1).
  lets H2_: hpstep_d_tick_inversion Hstep2; eauto.
  destruct H2_ as (t2 & ks2 & s2 & s2' & Hvc2 & Hsstp2 & Hget2 & Hset2 & Husteq2).
  assert (Htd: forall td, sdom O1 t1 td <-> sdom O2 t2 td). 
  {
    eapply same_cur_dom_t1t2_td; eauto.
  }

  lets H1_: Hsuc1 Hget1.
  assert (Hex1: exists vl1', has_tick ispc t1 cid O1 vl1' O1').
  {
    inverts Htr. inv_tuple.
    inv_hctr well_sched.
    lets H__: has_tick'_has_tick H1_ Hsstp1; eauto.
  }
  destruct Hex1 as (tl1' & Htck1).
  lets H2_: Hsuc2 Hget2.
  assert (Hex2: exists vl2', has_tick ispc t2 cid O2 vl2' O2').
  {
    inverts Htr. inv_tuple. 
    inv_hctr well_sched.
    lets H__: has_tick'_has_tick H2_ Hsstp2; eauto.
  }
  destruct Hex2 as (tl2' & Htck2).

  unfold obsr_equiv in Hoe_d.
  destruct Hoe_d as (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ & Heq1_ & Heq2_ & Hprogeq & Husteq & Hctideq & Hdteq).
  symmetry in Heq1_. symmetry in Heq2_.
  inverts Heq1_. inverts Heq2_.
  
  splits.
  4: { (* dteq *) 
    inverts Htr. inv_tuple.
    inv_hctr well_sched.
    unfolds in ws_tick_equiv.
    lets H__: ws_tick_equiv Hinv1 Hinv2 Hdteq_sch Hdteq.
    lets H_: H__ Htck1 Htck2.
    destruct H_; auto.
  }

  { (* prog_equiv *)
    assert (Hor: sdom O1 t1 i \/ ~sdom O1 t1 i) by tauto.
    destruct Hor as [Hsd1 | Hnsd1].

    - (* executing task is in dom i *) 
      unfolds in Hctideq.
      lets H__: Hctideq Hvc1 Hvc2 Hsd1.
      assert (Hsd2: sdom O2 t2 i).
      {
        eapply Htd in Hsd1; eauto.
      }
      subst t1.
      rename t2 into tx.
      unfolds.
      introv Hsd1' Hsd2'.
      casetac tx t He Hne.
      + subst.
        do 2 rewrite upd_task_pool_eq.
        unfolds in Hprogeq.
        lets H_: Hprogeq t Hsd1 Hsd2.
        Set Printing Implicit.
        unfold code in H_.
        asst_same_code T1 T2 t H_. inverts H_.
        Unset Printing Implicit.
        rename ks2 into ks. rename s2 into s.
        inv_tuple.
        
        inverts Htr. inv_tuple.
        inv_hctr well_sched.
        lets H_hstep: spec_step_head_step_tick Hsstp1 H1_ ws_ntck_knl; eauto.
        destruct H_hstep as (step & vl_ & Hhstep & Hall).
        assert
          (forall vl1' vl2',
              step t vl_ O1 (_TickAct cid) (vl1', O1') ->
              step t vl_ O2 (_TickAct cid) (vl2', O2')
              -> vl1' = vl2').
        {
          introv hstep1 hstep2.
          lets Htck1_: Hall hstep1.
          lets Htck2_: Hall hstep2.
          lets Hres_: ws_tick_equiv Hinv1 Hinv2 Hdteq_sch Hdteq Htck1_ Htck2_; eauto.
          apply Hres_.
        }
        lets H_: head_step_deter Hhstep.
        specializes H_; eauto.
        congruence.

        (* lets Hhstep: spec_step_head_step_fixed_vl' H4 Hsstp1 H1_. *)
        (* destruct Hhstep as (step & vl & Hhstep & Hall). *)
        (* lets Heqs': head_step_deter Hhstep Hall Hsstp1 Hsstp2; eauto. *)
        (* congruence.  *)
      +
        rewrite Hset1; rewrite Hset2.
        rewrite upd_task_pool_neq; eauto.
        rewrite upd_task_pool_neq; eauto.
        unfolds in Hprogeq.
        lets H_: Hgctrl1 Hget1; eauto.
        lets H__: good_stmt_spec_step_same_dom H_ Hinv1 Hsstp1.
        eapply H__ in Hsd1'; eauto. clear H_ H__.
        lets H_: Hgctrl2 Hget2; eauto.
        lets H__: good_stmt_spec_step_same_dom H_ Hinv2 Hsstp2.
        eapply H__ in Hsd2'; eauto.
        
    - (* ~sdom t1 O1 i *) 
      assert (Hnsd2: ~sdom O2 t2 i).
      {
        rewrite <- Htd. auto.
      }
      unfolds.
      introv Hsd1' Hsd2'.
      subst T1'. subst T2'.
      lets H_: Hgctrl1 Hget1; eauto.
      lets H__: good_stmt_spec_step_same_dom H_ Hinv1 Hsstp1.
      eapply H__ in Hsd1'; eauto. clear H_ H__.
      lets H_: Hgctrl2 Hget2; eauto.
      lets H__: good_stmt_spec_step_same_dom H_ Hinv2 Hsstp2.
      eapply H__ in Hsd2'; eauto. clear H_ H__.
      assert (Hnet1: t1 <> t).
      {
        casetac t1 t He Hne.
        - subst t1. apply Hnsd1 in Hsd1'. false. 
        - auto.
      }
      assert (Hnet2: t2 <> t).
      {
        casetac t2 t He Hne.
        - subst t2. apply Hnsd2 in Hsd2'. false. 
        - auto.
      }
      rewrite upd_task_pool_neq; eauto.
      rewrite upd_task_pool_neq; eauto.
  }

  { (* ust_equiv *) 
    subst; auto.
  }

  { (* ctid_equiv *)
    
    unfold ctid_equiv in *.
    introv Hgct1 Hgct2 Hsd.     
    lets Heq1: ct_spec_step_preserved Hsstp1.
    lets Heq2: ct_spec_step_preserved Hsstp2.
    eapply Heq1 in Hgct1.
    eapply Heq2 in Hgct2.
    lets H__: Hctideq Hgct1 Hgct2. 
    eapply H__; eauto. clear H__.
    lets H_: Hgctrl1 Hget1; eauto.
    lets H__: good_stmt_spec_step_same_dom H_ Hinv1 Hsstp1.
    eapply H__; eauto.
  }
Qed.


Lemma spec_steps_preserve_same_cur_dom:
  forall t1 t2 sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 s1 ks1 O2 s2 ks2 s1' s2' O1' O2' ac cid, 
    good_stmt t1 rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 s1 ks1 ->
    good_stmt t2 rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 s2 ks2 ->
    I O1 -> I O2 -> 
    spec_step sd t1 s1 O1 s1' O1' ac ->
    spec_step sd t2 s2 O2 s2' O2' ac ->
    cur_tsk O1 cid t1 ->
    cur_tsk O2 cid t2 -> 
    same_td_for_ct O1 O2 ->
    same_td_for_ct O1' O2'.    
Proof. 
  introv Hgstmt1 Hgstmt2 Hinv1 Hinv2 Hsstp1 Hsstp2 Hvc1 Hvc2 Hscd.
  assert (Htd: forall td, sdom O1 t1 td <-> sdom O2 t2 td). 
  {
    eapply same_cur_dom_t1t2_td; eauto.
  }
  (* destruct Htd as (td & Hsd1 & Hsd2). *) 
  unfold same_td_for_ct in *.
  intro cid0; specialize (Hscd cid0).
  destruct Hscd as (Heqv & Hall).  
  lets H1_: ct_spec_step_preserved Hsstp1; eauto.
  lets H2_: ct_spec_step_preserved Hsstp2; eauto.
  split.
  -
  split.
  + intros [t Hcur].
    assert (exists t, cur_tsk O1 cid0 t) as H_O1.
    {
      exists t.
      apply (proj2 (H1_ cid0 t)).
      exact Hcur.
    }

    destruct (proj1 Heqv H_O1) as [t' H_O2].
    exists t'.
    apply (proj1 (H2_ cid0 t')).
    exact H_O2.

  + intros [t Hcur].
    assert (exists t, cur_tsk O2 cid0 t) as H_O2.
    {
      exists t.
      apply (proj2 (H2_ cid0 t)).
      exact Hcur.
    }

    destruct (proj2 Heqv H_O2) as [t' H_O1].
    exists t'.
    apply (proj1 (H1_ cid0 t')).
    exact H_O1.
  -
    introv Hgt1 Hgt2.
    rewrite <- H1_ in Hgt1.
    rewrite <- H2_ in Hgt2.
    intro td.
    specialize (Htd td).
    lets H1__: good_stmt_spec_step_same_dom Hgstmt1 Hinv1 Hsstp1.
    lets H2__: good_stmt_spec_step_same_dom Hgstmt2 Hinv2 Hsstp2.
    rewrite <- H1__. rewrite <- H2__.
    eapply Hall; eauto.
Qed.


Lemma ticks_preserve_dteq_sched_dom: 
  forall rly_tsk guar_tsk rly_itp guar_itp flt (dteq: dt_obeq_t) uprgs aspc ispc sd O1 O2 O1' O2' 
         T1 T2 T1' T2' ust1 ust2 ust1' ust2' d1' d2' cid 
         (Htr : top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd))
         (Hsame_cd: same_cdom O1 O2) 
         (Hsame_curd : same_td_for_ct O1 O2) 
         (Hdteq_sch : dteq SchedDom O1 O2)
         (Hoe_d : obsr_equiv SchedDom dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hstep1 : hpstep_d uprgs (aspc, ispc, sd) (T1, ust1, O1) (T1', ust1', O1') (TickAct cid) d1')
         (Hstep2 : hpstep_d uprgs (aspc, ispc, sd) (T2, ust2, O2) (T2', ust2', O2') (TickAct cid) d2')
         (Hinv1 : I O1)
         (Hgctrl1 : forall (t : tid) (C : code),
             T1 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 C)
         (Hsuc1 : forall (t : tid) (C : code), T1 t = Some C -> ctrl_succ_eq aspc ispc C)
         (Hinv2 : I O2)
         (Hgctrl2 : forall (t : tid) (C : code),
             T2 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 C)
         (Hsuc2 : forall (t : tid) (C : code), T2 t = Some C -> ctrl_succ_eq aspc ispc C), 
    same_cdom O1' O2' /\ same_td_for_ct O1' O2' /\ dteq SchedDom O1' O2'. 

Proof.              
  intros.
  lets H1_: hpstep_d_tick_inversion Hstep1; eauto.
  destruct H1_ as (t1 & ks1 & s1 & s1' & Hvc1 & Hsstp1 & Hget1 & Hset1 & Hust1').
  lets H2_: hpstep_d_tick_inversion Hstep2; eauto.
  destruct H2_ as (t2 & ks2 & s2 & s2' & Hvc2 & Hsstp2 & Hget2 & Hset2 & Hust2').
  
  assert (Htd: forall td, sdom O1 t1 td <-> sdom O2 t2 td). 
  {
    eapply same_cur_dom_t1t2_td; eauto.
  }

  lets H1_: Hsuc1 Hget1.
  assert (Hex1: exists vl1', has_tick ispc t1 cid O1 vl1' O1').
  {
    inverts Htr. inv_tuple.
    inv_hctr well_sched.
    lets H__: has_tick'_has_tick H1_ Hsstp1; eauto.
  }
  destruct Hex1 as (tl1' & Htck1).
  lets H2_: Hsuc2 Hget2.
  assert (Hex2: exists vl2', has_tick ispc t2 cid O2 vl2' O2').
  {
    inverts Htr. inv_tuple.
    inv_hctr well_sched.
    lets H__: has_tick'_has_tick H2_ Hsstp2; eauto.
  }
  destruct Hex2 as (tl2' & Htck2).
  splits.
  - (* same_cdom *)
    unfold same_cdom in *.
    intros cid0 td.
    inverts Htr. inv_tuple.
    inverts H2.
    casetac cid cid0 He Hne.
    + 
      subst.
      lets H_: ws_tick_cdeq Hinv1 Hinv2; eauto.
    +
      assert (H11': cur_dom O1 cid0 td <-> cur_dom O1' cid0 td).
      {
        eapply ws_tick_prsv_cd; eauto.
      }
      assert (H22': cur_dom O2 cid0 td <-> cur_dom O2' cid0 td).
      {
        eapply ws_tick_prsv_cd; eauto.
      }
      specialize (Hsame_cd cid0 td).
      rewrite H11' in Hsame_cd. rewrite H22' in Hsame_cd.
      auto.
    
  - (* same_td_for_ct *)
    lets Hg1_: Hgctrl1 Hget1.
    destruct Hg1_ as (Hgs1 & Hgc1).
    lets Hg2_: Hgctrl2 Hget2.
    destruct Hg2_ as (Hgs2 & Hgc2).
    lets H_: spec_steps_preserve_same_cur_dom Hgs1 Hgs2 Hinv1 Hinv2.
    lets H__: H_ Hsstp1 Hsstp2 Hvc1 Hvc2.
    eapply H__; eauto.
    
  - (* dteq *)
    inverts Htr. inv_tuple.
    inv_hctr well_sched.
    unfolds in ws_tick_equiv.
    lets H__: ws_tick_equiv Hinv1 Hinv2 Hdteq_sch Hdteq_sch.
    lets H_: H__ Htck1 Htck2. clear H__.
    destruct H_; auto.
Qed. 


Lemma sched_indom_eq:
  forall (sd: ossched) O t td td', 
    I O -> 
    sd O td t -> 
    sdom O t td' ->
    sched_in_dom sd -> 
    (* sdom_is_func I sdom -> *)
    td = td'. 
Proof.
  introv Hinv Hsd Hsdom Hsid.
  assert (sdom O t td).
  { 
    eapply Hsid; eauto.
  }
  eapply sdom_is_fn; eauto.
Qed.

Lemma scheds_preserve_dteq_task_dom: 
  forall rly_tsk guar_tsk rly_itp guar_itp flt (dteq: dt_obeq_t) uprgs aspc ispc sd O1 O2 O1' O2' 
         T1 T2 T1' T2' ust1 ust2 ust1' ust2' d1' d2' cid i
         (Htr : top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd)) 
         (Hsame_cd: same_cdom O1 O2) 
         (Hsame_curd : same_td_for_ct O1 O2) 
         (Hdteq_sch : dteq SchedDom O1 O2)
         (Hoe_d : obsr_equiv (TaskDom i) dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hstep1 : hpstep_d uprgs (aspc, ispc, sd) (T1, ust1, O1) (T1', ust1', O1') (SwAct cid) d1')
         (Hstep2 : hpstep_d uprgs (aspc, ispc, sd) (T2, ust2, O2) (T2', ust2', O2') (SwAct cid) d2')
         (Hinv1 : I O1)
         (Hgctrl1 : forall (t : tid) (C : code),
             T1 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 C)
         (Hinv2 : I O2)
         (Hgctrl2 : forall (t : tid) (C : code),
             T2 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 C), 
    
    prog_equiv i T1' T2' O1' O2' /\
      ust_equiv i ust1' ust2' /\ 
      ctid_equiv i O1' O2' /\
      dteq (TaskDom i) O1' O2'. 
Proof.
  intros.
  lets H1_: hpstep_d_sched_inversion Hstep1.
  lets H2_: hpstep_d_sched_inversion Hstep2.
  destruct H1_ as
    (t1 & t1' & td1 & asrt1 & vs1 & ks1 &
       Hgct1 & Hcdom1 & Hsd1 & HO1' & Hust1' & HgT1 & HgT1').
  destruct H2_ as
    (t2 & t2' & td2 & asrt2 & vs2 & ks2 &
       Hgct2 & Hcdom2 & Hsd2 & HO2' & Hust2' & HgT2 & HgT2').
  assert (Htd: forall td, sdom O1 t1 td <-> sdom O2 t2 td). 
  {
    eapply same_cur_dom_t1t2_td; eauto.
  }
  
  unfolds in Hoe_d.
  destruct Hoe_d as
    (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ &
       Heq1_ & Heq2_ & Hprogeq & Husteq & Hctideq & Hdteq).
  symmetry in Heq1_; symmetry in Heq2_.
  inverts Heq1_; inverts Heq2_.
  
  splits.

  - (* prog_equiv *)
    unfolds.
    introv Hsdt1 Hsdt2.
    inverts Htr. inv_tuple.
    inverts H2.
    
    assert (Hsd1_: sdom O1 t i).
    {
      lets H_: ws_sched_eqdom Hinv1 Hcdom1 Hsd1 HO1'; eauto.
      eapply H_; eauto.
    }
    assert (Hsd2_: sdom O2 t i).
    {
      lets H_: ws_sched_eqdom Hinv2 Hcdom2 Hsd2 HO2'; eauto.
      eapply H_; eauto.
    }
    rewrite HgT1'. rewrite HgT2'.
    (* t1 and t2 are in dom td *) 

    assert (Hor: sdom O1 t1 i \/ ~sdom O1 t1 i) by tauto.
    destruct Hor as [Hsd1i | Hnsd1i].

    + (* dom of executing task is i *) 
      assert (Hteq: t1 = t2).
      {
        unfolds in Hctideq.
        lets H_: Hctideq Hgct1 Hgct2.
        eapply H_; eauto.
      }
      subst t1. rename t2 into tx.
      casetac tx t He Hne.
      * 
        subst tx.
        rewrite upd_task_pool_eq. 
        rewrite upd_task_pool_eq. 
        unfolds in Hprogeq.
        lets H_: Hprogeq Hsd1_ Hsd2_; eauto.
        Set Printing Implicit.
        unfold code in H_.
        rewrite HgT1 in H_.
        rewrite HgT2 in H_.
        inverts H_.
        auto.
        Unset Printing Implicit.
      *
        rewrite upd_task_pool_neq; eauto.
        rewrite upd_task_pool_neq; eauto.

    + (* dom of executing task is not i *) 
      assert (Hnsd2i: ~ sdom O2 t2 i).
      {
        rewrite <- Htd; eauto.
      }
      assert (Hneqt1: t1 <> t).
      {
        casetac t1 t He Hne.
        -
          subst t1.
          apply Hnsd1i in Hsd1_. false.
        -
          auto.
      }
      assert (Hneqt2: t2 <> t).
      {
        casetac t2 t He Hne.
        -
          subst t2.
          apply Hnsd2i in Hsd2_. false. 
        -
          auto.
      }
      rewrite upd_task_pool_neq; eauto.
      rewrite upd_task_pool_neq; eauto.

  - (* ust_equiv *)
    subst ust1'. subst ust2'. auto.

  - (* ctid_equiv *)
    unfold ctid_equiv in *.
    introv Hgetco1 Hgetco2 Hsdm.
    rename t0 into t1'_. rename t3 into t2'_.
    assert (Htde: td1 = td2).
    { 
      eapply Hsame_cd in Hcdom1.
      lets H__: cur_dom_is_fn Hcdom1 Hcdom2; eauto.
    }
    rename td2 into td.
    casetac cid cid0 He Hne.
    + (* cid = cid0 *)
      subst. 
      assert (Hct1': cur_tsk O1' cid0 t1').
      {
        eapply upd_cur_tsk_eq; eauto.
      }
      assert (Hct2': cur_tsk O2' cid0 t2').
      {
        eapply upd_cur_tsk_eq; eauto.
      }
      assert (Hinv1': I O1').
      {
        inverts Htr; inv_tuple.
        inverts H2.
        lets H_: ws_sched_inv Hinv1; eauto.
      }
      assert (Hinv2': I O2').
      {
        inverts Htr; inv_tuple.
        inverts H2.
        lets H_: ws_sched_inv Hinv2; eauto.
      }
      assert (H1eq: t1' = t1'_).
      {
        lets H__: cur_tsk_is_fn Hgetco1 Hct1'; eauto.
      }
      assert (H2eq: t2' = t2'_).
      {
        lets H__: cur_tsk_is_fn Hgetco2 Hct2'; eauto.
      }
      subst.
      inverts Htr; inv_tuple.
      inv_hctr well_sched.
      assert (Hsdtd: sdom O1 t1'_ td).
      { 
        eapply ws_sch_in_dom; eauto.
      }
      assert (Hsdtd1': sdom O1' t1'_ td).
      {
        lets H__: ws_sched_eqdom Hinv1 Hcdom1 Hsd1 HO1'; eauto.
        eapply H__; eauto.        
      }
      assert (Htdi: i = td).
      {
        clear -Hinv1' Hsdm Hsdtd1'.
        eapply sdom_is_fn; eauto.
      }
      subst.
      lets H_: ws_sched_eqchoi Hinv1 Hinv2 Hdteq.
      eapply H_ in Hsd1.
      clear -ws_sd_fn Hinv2 Hsd1 Hsd2.
      eapply ws_sd_fn; eauto.

    + (* cid <> cid0 *)
      lets H1_: upd_cur_tsk_neq (not_eq_sym Hne)  HO1'.
      lets H2_: upd_cur_tsk_neq (not_eq_sym Hne)  HO2'.
      assert (Hct1_: cur_tsk O1 cid0 t1'_).
      {
        eapply H1_; eauto.
      }
      assert (Hct2_: cur_tsk O2 cid0 t2'_).
      {
        eapply H2_; eauto.
      }
      lets H__: Hctideq Hct1_ Hct2_.
      eapply H__; eauto. clear H__.
      inverts Htr; inv_tuple.      
      lets H__: ws_sched_eqdom Hinv1 Hcdom1 Hsd1 HO1'; eauto.
      eapply H__; eauto.
    
  - (* dteq *)
    assert (H11': dteq (TaskDom i) O1 O1').
    {
      inverts Htr; inv_tuple.
      inv_hctr well_sched.
      eapply ws_swi_dteq; eauto.
    }
    assert (H22': dteq (TaskDom i) O2 O2').
    {
      inverts Htr; inv_tuple.
      inv_hctr well_sched.
      eapply ws_swi_dteq; eauto.
    }
    inverts Htr; inv_tuple.
    inv_hctr good_dteq.
    specialize (gd_equiv_rel (TaskDom i)).
    inverts gd_equiv_rel.
    assert (H1'1: dteq (TaskDom i) O1' O1).
    {
      eapply Equivalence_Symmetric; eauto.
    }
    assert (H1'2: dteq (TaskDom i) O1' O2).
    {
      eapply Equivalence_Transitive; eauto.
    }
    clear H1'1.
    eapply Equivalence_Transitive; eauto.
Qed. 

Lemma scheds_preserve_dteq_sched_dom:
  forall rly_tsk guar_tsk rly_itp guar_itp flt (dteq: dt_obeq_t) uprgs aspc ispc sd O1 O2 O1' O2' 
         T1 T2 T1' T2' ust1 ust2 ust1' ust2' d1' d2' cid 
         (Htr : top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd))
         (Hsame_cd: same_cdom O1 O2)
         (Hsame_curd : same_td_for_ct O1 O2)
         (Hdteq_sch : dteq SchedDom O1 O2)
         (Hoe_d : obsr_equiv SchedDom dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hstep1 : hpstep_d uprgs (aspc, ispc, sd) (T1, ust1, O1)
                     (T1', ust1', O1') (SwAct cid) d1')
         (Hstep2 : hpstep_d uprgs (aspc, ispc, sd) (T2, ust2, O2) 
                     (T2', ust2', O2') (SwAct cid) d2')
         (Hinv1 : I O1)
         (Hgctrl1 : forall (t : tid) (C : code),
             T1 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 C)
         (Hinv2 : I O2)
         (Hgctrl2 : forall (t : tid) (C : code),
             T2 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 C), 
    same_cdom O1' O2' /\ same_td_for_ct O1' O2' /\ dteq SchedDom O1' O2'.  
Proof.
  intros.
  lets H1_: hpstep_d_sched_inversion Hstep1.
  lets H2_: hpstep_d_sched_inversion Hstep2.
  destruct H1_ as
    (t1 & t1' & td1 & asrt1 & vs1 & ks1 &
       Hgct1 & Hcdom1 & Hsd1 & HO1' & Hust1' & HgT1 & HgT1').
  destruct H2_ as
    (t2 & t2' & td2 & asrt2 & vs2 & ks2 &
       Hgct2 & Hcdom2 & Hsd2 & HO2' & Hust2' & HgT2 & HgT2').
  assert (Htd: forall td, sdom O1 t1 td <-> sdom O2 t2 td). 
  {
    eapply same_cur_dom_t1t2_td; eauto.
  }

  (* unfolds in Hoe_d. *)
  (* destruct Hoe_d as *)
  (*   (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ & Heq1_ & Heq2_ & Hscd & Hsctd & Hdteq). *)
  (* symmetry in Heq1_; symmetry in Heq2_. *)
  (* inverts Heq1_; inverts Heq2_.   *)

  splits.

  - (* same_cdom *)
    inverts Htr; inv_tuple.
    inv_hctr well_sched.
    lets H1_: sched_same_cur_dom Hinv1 Hcdom1 Hsd1 HO1'; eauto.
    lets H2_: sched_same_cur_dom Hinv2 Hcdom2 Hsd2 HO2'; eauto.
    unfolds. intros. 
    rewrite <- H1_. rewrite <- H2_.
    auto.
  
  - (*same_td_for_ct *)
    unfolds.
    intros.
    assert (Hor: cid = cid0 \/ cid <> cid0) by tauto.
    destruct Hor.
    
    + (* cid = cid0 *)
      subst.
      unfolds in Hsame_curd.
      specialize (Hsame_curd cid0).
      destruct Hsame_curd as (Heqv & Hsdeq).
      assert (Hct1': cur_tsk O1' cid0 t1').
      {
        eapply upd_cur_tsk_eq; eauto.
      }
      assert (Hct2': cur_tsk O2' cid0 t2').
      {
        eapply upd_cur_tsk_eq; eauto.
      }
      split.
      * 
        split; intros; eexists; eauto.
      *
        introv Hct1'_ Hct2'_.
        assert (Hinv1': I O1').
        {
          inverts Htr; inv_tuple.
          inverts H2.
          lets H_: ws_sched_inv Hinv1; eauto.
        }
        assert (Hinv2': I O2').
        {
          inverts Htr; inv_tuple.
          inverts H2.
          lets H_: ws_sched_inv Hinv2; eauto.
        }
        lets H1_: cur_tsk_is_fn Hinv1' Hct1' Hct1'_.
        lets H2_: cur_tsk_is_fn Hinv2' Hct2' Hct2'_.
        symmetry in H1_. symmetry in H2_.
        subst.
        assert (td1 = td2).
        {
          eapply Hsame_cd in Hcdom1; eauto.
          lets H_: cur_dom_is_fn Hcdom1 Hcdom2; eauto.
        }
        subst td1. rename td2 into tdx. 
        assert (H1_: sdom O1 t1' tdx).
        {
          inverts Htr; inv_tuple.
          inverts H2.
          eapply ws_sch_in_dom; eauto.
        }
        assert (H2_: sdom O2 t2' tdx).
        {
          inverts Htr; inv_tuple.
          inverts H2.
          eapply ws_sch_in_dom; eauto.
        }
        intros.
        inverts Htr; inv_tuple.
        inv_hctr well_sched.
        lets H1__: ws_sched_eqdom Hinv1 Hcdom1 Hsd1 HO1'.
        lets H2__: ws_sched_eqdom Hinv2 Hcdom2 Hsd2 HO2'.
        split.
        ** introv Hsd1'_.
           eapply H1__ in Hsd1'_.
           lets H__: sdom_is_fn H1_ Hsd1'_; eauto.
           subst.
           eapply H2__; eauto.
        ** introv Hsd2'_.
           eapply H2__ in Hsd2'_.
           lets H__: sdom_is_fn H2_ Hsd2'_; eauto.
           subst.
           eapply H1__; eauto.

    + (* cid <> cid0 *)
      specialize (Hsame_curd cid0).
      destruct Hsame_curd as (Heqv & Hall). 
      split.
      *
        split.
        **
          introv Hct1'. destruct Hct1' as (t1'_ & Hct1').
          assert (Hct1_: cur_tsk O1 cid0 t1'_).
          {
            lets H_: upd_cur_tsk_neq (not_eq_sym H0) HO1'. eapply H_; eauto.
          }
          assert (Hex: exists t, cur_tsk O2 cid0 t).
          {
            eapply Heqv; eauto.
          }
          destruct Hex as (t2'_ & Hct2').
          exists t2'_.
          lets H_: upd_cur_tsk_neq (not_eq_sym H0) HO2'. eapply H_; eauto.
        **
          introv Hct2'. destruct Hct2' as (t2'_ & Hct2').
          assert (Hct2_: cur_tsk O2 cid0 t2'_).
          {
            lets H_: upd_cur_tsk_neq (not_eq_sym H0) HO2'. eapply H_; eauto.
          }
          assert (Hex: exists t, cur_tsk O1 cid0 t).
          {
            eapply Heqv; eauto.
          }
          destruct Hex as (t1'_ & Hct1').
          exists t1'_.
          lets H_: upd_cur_tsk_neq (not_eq_sym H0) HO1'. eapply H_; eauto.
      *
        introv Hct1' Hct2'.
        rename t0 into t1'_.
        rename t3 into t2'_.
        lets H_: upd_cur_tsk_neq (not_eq_sym H0) HO1'.
        eapply H_ in Hct1'; clear H_.
        lets H_: upd_cur_tsk_neq (not_eq_sym H0) HO2'.
        eapply H_ in Hct2'; clear H_.
        lets H__: Hall Hct1' Hct2'.
        intros.
        specialize (H__ td).
        inverts Htr; inv_tuple.
        inv_hctr well_sched.
        
        lets H1_: ws_sched_eqdom Hinv1 Hcdom1 Hsd1 HO1'.
        lets H2_: ws_sched_eqdom Hinv2 Hcdom2 Hsd2 HO2'.
        rewrite <- H1_. rewrite <- H2_.
        auto.
        
  - (* dteq *)
    assert (H11': dteq SchedDom O1 O1').
    {
      inverts Htr; inv_tuple.
      inv_hctr well_sched.
      eapply ws_swi_dteq; eauto.
    }
    assert (H22': dteq SchedDom O2 O2').
    {
      inverts Htr; inverts H.
      inv_hctr well_sched.
      eapply ws_swi_dteq; eauto.
    }
    inverts Htr; inv_tuple.
    inv_hctr good_dteq.
    specialize (gd_equiv_rel SchedDom).
    inverts gd_equiv_rel.
    assert (H1'1: dteq SchedDom O1' O1).
    {
      eapply Equivalence_Symmetric; eauto.
    }
    assert (H1'2: dteq SchedDom O1' O2).
    {
      eapply Equivalence_Transitive; eauto.
    }
    clear H1'1.
    eapply Equivalence_Transitive; eauto.
Qed.

Lemma hpstep_d_hpstep:
  forall uprgs aspc ispc sd T ust O T' ust' O' ac d, 
    hpstep_d uprgs (aspc, ispc, sd) (T, ust, O) (T', ust', O') ac d ->
    ~sched_act ac ->
    exists t td, 
      hpstep uprgs (aspc, ispc, sd) T ust O T' ust' O' (ac, t) /\
        d = TaskDom td /\ 
        sdom O t td.
Proof.
  introv Hstep Hnsa.
  inverts Hstep.
  -
    do 2 eexists; splits; eauto.
  -
    false.
    apply Hnsa.
    unfolds.
    rn_or Hor.
    destruct Hor; subst ac; eauto.
Qed. 

Lemma hpsetp_valid_ct:
  forall uprgs aspc ispc sd T ust O T' ust' O' ac t, 
    hpstep uprgs (aspc, ispc, sd) T ust O T' ust' O' (ac, t) ->
    exists cid, cur_tsk O cid t.
Proof.
  introv Hstep.
  inverts Hstep; eexists; eauto.
Qed. 

Lemma obequiv_vc_tideq:
  forall td dteq T1 ust1 O1 T2 ust2 O2 cid t1 t2, 
    obsr_equiv (TaskDom td) dteq (T1, ust1, O1) (T2, ust2, O2) ->
    cur_tsk O1 cid t1 ->
    cur_tsk O2 cid t2 -> 
    sdom O1 t1 td ->
    t1 = t2. 
Proof.
  introv Hoe Hvc1 Hvc2 Hsd.
  unfolds in Hoe.
  simpljoin.
  unfolds in H3.
  specializes H3; eauto.
Qed. 

Lemma obequiv_prog_eq:
  forall td dteq T1 ust1 O1 T2 ust2 O2 t, 
    obsr_equiv (TaskDom td) dteq (T1, ust1, O1) (T2, ust2, O2) ->
    sdom O1 t td ->
    sdom O2 t td ->
    T1 t = T2 t.
Proof.
  introv Hoe Hsd1 Hsd2.
  unfolds in Hoe.
  simpljoin.
  unfolds in H2.
  eapply H2; eauto.
Qed.

Lemma obequiv_ust_eq:
  forall td dteq T1 ust1 O1 T2 ust2 O2, 
    obsr_equiv (TaskDom td) dteq (T1, ust1, O1) (T2, ust2, O2) ->
    get ust1 td = get ust2 td. 
Proof.
  introv Hoe.
  unfolds in Hoe.
  simpljoin.
  unfolds in H2.
  auto.
Qed. 
    
Lemma good_ctrl_hpstep_ctid_dom_preserved:
  forall rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs aspc ispc sd t T O T' O' ac ust ust',
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd) -> 
    I O -> 
    (forall (t : tid) (C : code),
        T t = Some C ->
        good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O C) -> 
    (* good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp I sdom flt dteq O C -> *)
    hpstep uprgs (aspc, ispc, sd) T ust O T' ust' O' (ac, t) ->
    (~exists cid, ac = SwAct cid) -> 
    ((forall cid t, cur_tsk O cid t <-> cur_tsk O' cid t) /\ (forall t td, sdom O t td <-> sdom O' t td)). 
Proof.
  introv Htr Hinv Hgctrl Hstep Hnswi.
  assert (HgTt: exists C, T t = Some C).
  { inv_hpstep; eexists; eauto. }
  destruct HgTt as (C & HgTt).
  specialize (Hgctrl _ _ HgTt).  
  inverts Hstep.
  -
    (* destruct H8 as [Htck | Hntck]. *)
    inv_htstep.
    + destruct H8 as [Htck | Hntck].
      simpljoin; tryfalse.
      destruct Hntck; subst ac.
      split; auto.
      intros.
      split; intros; auto.
      intros. split; auto.
    + inv_hapistep;
        try (split; auto; intros; split; intros; auto; fail). 
      {
        unfolds in Hgctrl.
        destruct C. destruct c.
        2: { asst_same_code21 T t. inverts HC. }
        destruct Hgctrl as (Hgstmt & Hgcont).
        simpl in H1.
        asst_same_code21 T t. inverts HC.
        lets H_: ct_spec_step_preserved H1; eauto.
        lets H__: good_stmt_spec_step_same_dom Hgstmt Hinv; eauto.
      }
  -
    inv_htistep.
    split; auto; intros; split; intros; auto.
  -
    false. apply Hnswi; eexists; eauto.
  -
    inv_htstep.
    inv_hapistep.
    unfolds in Hgctrl.
    destruct C. destruct c.
    2: { asst_same_code21 T t. inverts HC. }
    destruct Hgctrl as (Hgstmt & Hgcont).
    simpl in H1.
    asst_same_code21 T t. inverts HC.
    lets H_: ct_spec_step_preserved H1; eauto.
    lets H__: good_stmt_spec_step_same_dom Hgstmt Hinv; eauto.
  -
    inv_htstep.
    inv_hapistep.
    unfolds in Hgctrl.
    destruct C. destruct c.
    2: { asst_same_code21 T t. inverts HC. }
    destruct Hgctrl as (Hgstmt & Hgcont).
    simpl in H1.
    asst_same_code21 T t. inverts HC.
    lets H_: ct_spec_step_preserved H1; eauto.
    lets H__: good_stmt_spec_step_same_dom Hgstmt Hinv; eauto.
Qed.     

Lemma good_ctrl_hpstep_scd_ctideq:
  forall rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs aspc ispc sd t T O T' O' ac ust ust',
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd) -> 
    I O -> 
    (forall (t : tid) (C : code),
        T t = Some C ->
        good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O C) ->  
    hpstep uprgs (aspc, ispc, sd) T ust O T' ust' O' (ac, t) ->
    (~exists cid, ac = SwAct cid) -> 
    (same_td_for_ct O O' /\ (forall td, ctid_equiv td O O')). 
Proof.
  introv Htr Hinv Hgctrl Hstep Hnsw.
  lets H__: good_ctrl_hpstep_ctid_dom_preserved Htr Hinv Hgctrl Hstep Hnsw.
  destruct H__ as (Hceq & Hsdeq).
  (* assert (Hex: exists ct cid, get O coretid = Some (oscoret ct) /\ get ct cid = Some t). *)
  (* { inverts Hstep; eexists; eauto. } *)
  assert (Hex: exists cid, cur_tsk O cid t).
  { inverts Hstep; eauto. } 
  destruct Hex as (cid & Hgct).
  assert (Hgct': cur_tsk O' cid t).
  { eapply Hceq; eauto. } 
  split.

  - (* same_td_for_ct *)  
    unfolds.
    intro cid0.
    split.
    + split; intros; auto.
      * destruct H0 as (t_ & Hct).
        eapply Hceq in Hct; eauto.
      * destruct H0 as (t_ & Hct').
        eapply Hceq in Hct'; eauto.
    +
      introv Hct1 Hct2.
      assert (t1 = t2).
      {
        eapply Hceq in Hct2.
        eapply cur_tsk_is_fn; eauto.
      }
      subst.
      intros.
      eapply Hsdeq; eauto.

  - (* ctid_equiv *)
    intro td.
    unfold ctid_equiv.
    introv Hgct_ Hgct'_ Hsd.
    eapply Hceq in Hgct'_.
    eapply cur_tsk_is_fn; eauto.
Qed. 

Lemma not_sch_act_not_swact:
  forall ac, ~ sched_act ac -> ~ (exists cid, ac = SwAct cid).
Proof.
  introv Hncha.
  introv Hex. apply Hncha.
  destruct Hex.
  unfolds.
  subst ac.
  auto.
Qed. 

Lemma not_sch_act_not_tckact:
  forall ac, ~ sched_act ac -> ~ (exists cid, ac = TickAct cid).
Proof.
  introv Hncha.
  introv Hex. apply Hncha.
  destruct Hex.
  unfolds.
  subst ac.
  auto.
Qed. 

Ltac destruct_oe_taskd H :=
  let Hprge := fresh "Hprge" in
  let Huste := fresh "Huste" in
  let Hctide := fresh "Hctide" in
  let Hdte := fresh "Hdte" in 
  destruct H as (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ & Heq11_ & Heq22_ & Hprge & Huste & Hctide & Hdte).


Lemma hpstep2_not_sched_ctid_equiv_preserved:
  forall rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs aspc ispc sd O1 O2 T1 T2 ust1 ust2 O1' O2' T1' T2' ust1' ust2' ac t i
         (Htr : top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd))
         (Hsame_curd : same_td_for_ct O1 O2) 
         (Hoe_d : obsr_equiv (TaskDom i) dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hgctrl1 : forall (t : tid) (C : code),
             T1 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 C)
         (Hgctrl2 : forall (t : tid) (C : code), 
             T2 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 C)
         (Hnschac : ~ sched_act ac)
         (Hinv1 : I O1)
         (Hinv2 : I O2) 
         (Hstep1 : hpstep uprgs (aspc, ispc, sd) T1 ust1 O1 T1' ust1' O1' (ac, t))
         (Hstep2 : hpstep uprgs (aspc, ispc, sd) T2 ust2 O2 T2' ust2' O2' (ac, t)),
    ctid_equiv i O1' O2'.
Proof.
  intros. 
  lets Hce11'_: good_ctrl_hpstep_scd_ctideq Htr Hinv1 Hgctrl1 Hstep1.
  specialize (Hce11'_ (not_sch_act_not_swact ac Hnschac)).
  destruct Hce11'_ as (Hscd11' & Hcteq11').
  lets Hce1'1: ctid_equiv_sym_scd Hscd11' (Hcteq11' i).
  lets Hscd1'1: same_td_for_ct_sym Hscd11'.
  unfolds in Hoe_d.
  destruct_oe_taskd Hoe_d.
  inv_tuple.
  inv_tuple.
  lets Hce1'2: ctid_equiv_trans_scd Hscd1'1 Hce1'1 Hctide.
  lets Hscd1'2: same_td_for_ct_trans Hscd1'1 Hsame_curd. 
  lets Hce22'_: good_ctrl_hpstep_scd_ctideq Htr Hinv2 Hgctrl2 Hstep2.
  specialize (Hce22'_ (not_sch_act_not_swact ac Hnschac)).
  destruct Hce22'_ as (Hscd22' & Hcteq22').
  lets H__: ctid_equiv_trans_scd Hscd1'2 Hce1'2 (Hcteq22' i).
  auto.
Qed. 

Lemma prog_equiv_preserved:
  forall T1 T2 t i C O1 O2, 
    prog_equiv i T1 T2 O1 O2 -> 
    prog_equiv i (upd_task_pool T1 t C) (upd_task_pool T2 t C) O1 O2.
Proof.
  introv Hpe.
  unfolds.
  introv Hsd1 Hsd2.
  casetac t t0 He Hne.
  * subst. do 2 rewrite upd_task_pool_eq; auto.
  * repeat rewrite upd_task_pool_neq; eauto.
Qed.         

Lemma ust_equiv_preserved:
  forall (i: task_dom) ust1 ust2 sst td, 
    ust_equiv i ust1 ust2 ->
    ust_equiv i (set ust1 td sst) (set ust2 td sst).
Proof.
  introv Hue.        
  unfolds.
  destruct (Int.eq_dec td i).
  * subst. do 2 rewrite map_get_set; auto.
  * repeat rewrite neq_set_get; eauto.      
Qed. 

Lemma spec_step2_dteq_preserved: 
  forall t sd rly guar flt dteq s q, 
    deduct_rules t rly guar flt dteq s q ->    
    (* good_flt flt ->  *)
    forall O1 O2 O1' O2' td i s1' s2' ac1 ac2, 
      I O1 ->
      I O2 ->
      head_sat t O1 s ->
      head_sat t O2 s ->
      dteq (TaskDom i) O1 O2 ->
      flt (TaskDom td) (TaskDom i) ->
      dteq (TaskDom td) O1 O2 ->
      sdom O1 t td -> 
      sdom O2 t td -> 
      spec_step sd t s O1 s1' O1' ac1 ->
      spec_step sd t s O2 s2' O2' ac2 ->
      ~(exists cid, ac1 = _TickAct cid) ->
      ~(exists cid, ac2 = _TickAct cid) -> 
      s1' = s2' /\ ac1 = ac2 /\ dteq (TaskDom i) O1' O2'.
Proof.
  introv Hdr (* Hgflt *). 
  induction Hdr; 
  introv Hinv1 Hinv2 Hhs1 Hhs2 Hdteq_i Hflt Hdteq_td Hsdom1 Hsdom2;
  introv Hstep1 Hstep2; 
  introv Hntck1 Hntck2.
  
  -
    simpl in Hhs1.
    simpl in Hhs2.
    assert (Hpre2: pre2 t O1 O2 p i dobeq flt).
    {
      unfolds.
      splits; eauto.
      unfolds; split; eauto.
      unfolds; split; eauto.
    }
    inverts Hstep1; inverts Hstep2.
    lets H__: H2 Hpre2 H8 H9 Hntck1 Hntck2; eauto.
    destructs H__.
    splits; eauto.
    congruence.
    
  -
    simpl in Hhs1.
    simpl in Hhs2.
    
    inverts Hstep1; inverts Hstep2.
    + 
      lets H__: IHHdr Hinv1 Hinv2 Hhs1 Hhs2.
      lets H_: H__ Hdteq_i Hflt Hdteq_td Hsdom1 Hsdom2. clear H__.
      specializes H_; eauto.
      destructs H_; splits; eauto.
      congruence.
    +
      lets H__: IHHdr Hinv1 Hinv2 Hhs1 Hhs2.
      lets H_: H__ Hdteq_i Hflt Hdteq_td Hsdom1 Hsdom2. clear H__.
      specializes H_; eauto.
      destruct H_ as (Hs'eq & _ & _).
      subst.
      false. apply H11. eexists; eauto.
    +
      lets H__: IHHdr Hinv1 Hinv2 Hhs1 Hhs2.
      lets H_: H__ Hdteq_i Hflt Hdteq_td Hsdom1 Hsdom2. clear H__.
      specializes H_; eauto.
      destruct H_ as (Hs'eq & _ & _).
      subst.
      false.
      apply H10; eexists; eauto.
    +
      lets H__: IHHdr Hinv1 Hinv2 Hhs1 Hhs2.
      lets H_: H__ Hdteq_i Hflt Hdteq_td Hsdom1 Hsdom2. clear H__.
      specializes H_; eauto.
      destruct H_ as (Hs'eq & Haceq & Hdobeq).
      splits; eauto.
      congruence.
      
  -
    inverts Hstep1; inverts Hstep2; splits; eauto.

  -
    inverts Hstep1; inverts Hstep2; splits; eauto.

  -
    inverts Hstep1.
Qed.
  
Lemma hpstep_d2_same_td:
  forall T1 ust1 O1 T2 ust2 O2  T1' ust1' O1' T2' ust2' O2' ac d1' d2' dteq aspc ispc sd uprgs
         (Hinv1: I O1)
         (Hinv2: I O2) 
         (Hsame_curd : same_td_for_ct O1 O2)
         (Hdteq_sch : dteq SchedDom O1 O2)
         (Hnschac : ~ sched_act ac)
         (* (Hoe_d : obsr_equiv (TaskDom i) dteq (T1, ust1, O1) (T2, ust2, O2)) *)
         (* (Hoe_d' : flt d1' (TaskDom i) -> obsr_equiv d1' dteq (T1, ust1, O1) (T2, ust2, O2)) *)
         (Hstep1 : hpstep_d uprgs (aspc, ispc, sd) (T1, ust1, O1) (T1', ust1', O1') ac d1')
         (Hstep2 : hpstep_d uprgs (aspc, ispc, sd) (T2, ust2, O2) (T2', ust2', O2') ac d2'),
    d1' = d2'. 
Proof.
  intros.
  unfolds in Hsame_curd.
  lets H1_: hpstep_d_hpstep Hstep1 Hnschac. clear Hstep1.
  destruct H1_ as (t1 & td1 & Hstep1 & Hd'1 & Hsdom1).
  lets H2_: hpstep_d_hpstep Hstep2 Hnschac. clear Hstep2.
  destruct H2_ as (t2 & td2 & Hstep2 & Hd'2 &  Hsdom2).
  assert (Hex: exists cid, cur_tsk O1 cid t1 /\ cur_tsk O2 cid t2).
  {
    inverts Hstep1; inverts Hstep2; 
      try (
          repeat match goal with
              H: _ \/ _ |- _ =>
                destruct H; simpljoin; try discriminate; tryfalse
            end; 
          match goal with
          | H: TickAct _ = TickAct _ |- _ =>
              inverts H; eexists; split; eauto
          | H: SwAct _ = SwAct _ |- _ =>
              inverts H; eexists; split; eauto
          | H: TauAct _ = TauAct _ |- _ => 
              inverts H; eexists; split; eauto
          | H: EniAct _ _ = EniAct _ _ |- _ => 
              inverts H; eexists; split; eauto     
          end; 
          fail); try (eexists; split; eauto).
  }
  destruct Hex as (cid & Hct1 & Hct2).
  specialize (Hsame_curd cid).
  destruct Hsame_curd as (Heqv & Hall).
  specialize (Hall _ _ Hct1 Hct2).
  eapply Hall in Hsdom1.
  lets H__: sdom_is_fn Hsdom1 Hsdom2; eauto.
  congruence. 
Qed.
    
Definition core_of_ac (ac: sec_act) :=
  match ac with
    TauAct cid | EniAct cid _ | TickAct cid | SwAct cid => cid
  end.

Lemma task_steps_preserve_dteq:
  forall rly_tsk guar_tsk rly_itp guar_itp flt (dteq: dt_obeq_t) uprgs aspc ispc sd O1 O2 O1' O2' 
         T1 T2 T1' T2' ust1 ust2 ust1' ust2' d1' d2' d ac
         (Htr : top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd))
         (Hgflt : good_flt flt)
         (Hsame_cd: same_cdom O1 O2) 
         (Hsame_curd : same_td_for_ct O1 O2) 
         (Hdteq_sch : dteq SchedDom O1 O2)
         (Hoe_d : obsr_equiv d dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hoe_d' : flt d1' d -> obsr_equiv d1' dteq (T1, ust1, O1) (T2, ust2, O2))
         (Hstep1 : hpstep_d uprgs (aspc, ispc, sd) (T1, ust1, O1) (T1', ust1', O1') ac d1')
         (Hstep2 : hpstep_d uprgs (aspc, ispc, sd) (T2, ust2, O2) (T2', ust2', O2') ac d2')
         (Hinv1 : I O1)
         (Hgctrl1 : forall (t : tid) (C : code),
             T1 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O1 C)
         (* (Hcc1 : ct_core O1) *)
         (Hsuc1 : forall (t : tid) (C : code), T1 t = Some C -> ctrl_succ_eq aspc ispc C)
         (Hinv2 : I O2)
         (Hgctrl2 : forall (t : tid) (C : code),
             T2 t = Some C ->
             good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O2 C)
         (* (Hcc2 : ct_core O2) *) 
         (Hsuc2 : forall (t : tid) (C : code), T2 t = Some C -> ctrl_succ_eq aspc ispc C)
         (Hflt : flt d1' d)
         (Hnschac : ~ sched_act ac),
    obsr_equiv d dteq (T1', ust1', O1') (T2', ust2', O2').     
Proof.
  intros.
  destruct d.
  2: { (* d is SchedDom --- impossible *) 
    unfolds in Hgflt.
    eapply Hgflt in Hflt; eauto.
    inverts Hstep1.
    inverts H0.
    false. apply Hnschac. unfolds.
    rn_or Hor.
    destruct Hor; subst ac; simpl; auto.
  }

  assert (Hd'eq: d1' = d2').
  {
    lets H_: hpstep_d2_same_td Hinv1 Hinv2; eauto.
  }

  subst. rename d2' into d'.
  
  lets H1_: hpstep_d_hpstep Hstep1 Hnschac. clear Hstep1.
  destruct H1_ as (t1 & td1 & Hstep1 & Hd'1 & Hsdom1).
  lets H2_: hpstep_d_hpstep Hstep2 Hnschac. clear Hstep2.
  destruct H2_ as (t2 & td2 & Hstep2 & Hd'2 &  Hsdom2).
  rewrite Hd'1 in Hd'2.
  inverts Hd'2.
  rename td2 into td.
  specialize (Hoe_d' Hflt).
  subst d'.

  assert (Hex1: exists cid, cur_tsk O1 cid t1 /\ core_of_ac ac = cid).
  {
    inverts Hstep1;
      try (match goal with H: _ \/ _ |- _ => destruct H; simpljoin end; 
           try (eexists; splits; simpl; eauto); fail); try (eexists; splits; simpl; eauto).
  }
  assert (Hex2: exists cid, cur_tsk O2 cid t2 /\ core_of_ac ac = cid).
  {
    inverts Hstep2;
      try (match goal with H: _ \/ _ |- _ => destruct H; simpljoin end; 
           try (eexists; splits; simpl; eauto); fail); try (eexists; splits; simpl; eauto).
  }
  destruct Hex1 as (cid1 & Hct1 & Hcid1).
  destruct Hex2 as (cid2 & Hct2 & Hcid2).
  rewrite Hcid1 in Hcid2. clear Hcid1. subst.
  rename cid2 into cid.

  assert (Htideq: t1 = t2).
  {
    eapply obequiv_vc_tideq; eauto.
  }
  subst t1. rename t2 into t.

  assert (HTteq: T1 t = T2 t).
  {
    eapply obequiv_prog_eq; eauto.
  }

  assert (Husteq: get ust1 td = get ust2 td).
  {
    eapply obequiv_ust_eq; eauto.
  }

  unfolds.
  do 6 eexists; do 2 split; eauto.
  
  assert (Hctideq': ctid_equiv i O1' O2').
  { 
    eapply hpstep2_not_sched_ctid_equiv_preserved; eauto.
  }
  enough
    (Hrest :
      prog_equiv i T1' T2' O1' O2' /\
        ust_equiv i ust1' ust2' /\
        dteq (TaskDom i) O1' O2').
  {
    destruct Hrest as [Hprog [Hust Hdteq]].
    splits; eauto.
  }  
  lets H__: hpstep2_inversion Hstep1 Hstep2. 
  lets Hstep2_cases: H__ HTteq Hinv1 Hinv2 Hsdom1 Hsdom2.
  clear H__.
  specializes Hstep2_cases; eauto.
  destruct Hstep2_cases as
    [Husr_steps |
      [Henapi_steps | [Henitp_steps |
                        [Hexapi_steps | [Hexitp_steps |
                                          Hspec_steps]]]]].
  
  - (* two user steps *)
    simpljoin.
    destruct_oe_taskd Hoe_d.
    do 2 inv_tuple_rev. 
    splits; eauto.
    eapply ust_equiv_preserved; eauto.
    
  - (* two API calls *)
    simpljoin.
    destruct_oe_taskd Hoe_d.
    do 2 inv_tuple_rev. 
    splits; eauto.
    + (* prog_equiv *)
      eapply prog_equiv_preserved; eauto.
    + (* ust_equiv *)
      eapply ust_equiv_preserved; eauto.
      
  - (* two steps entering some interrupt handler *)
    simpljoin.
    destruct_oe_taskd Hoe_d.
    do 2 inv_tuple_rev. 
    splits; eauto.
    (* prog_equiv *)
    eapply prog_equiv_preserved; eauto.
  - (* two returns from some API function *)
    simpljoin.
    destruct_oe_taskd Hoe_d.
    do 2 inv_tuple_rev. 
    splits; eauto.
    + (* prog_equiv *)
      eapply prog_equiv_preserved; eauto.
    + (* ust_equiv *)
      eapply ust_equiv_preserved; eauto.
      
  - (* two steps exiting from some interrupt handler *)
    simpljoin.
    destruct_oe_taskd Hoe_d.
    do 2 inv_tuple_rev. 
    splits; eauto.
    eapply prog_equiv_preserved; eauto.
    
  - (* two spec_step's *)
    destruct Hspec_steps as
      (s & ks & s1' & s2' & ac1 & ac2 & cid_ &
         Hac & HgC1 & Hspstp1 & Hspstp2 & Hntck1 & Hntck2 & Hac1_cases & Hac2_cases & Hust1' & Hust2').
    subst ust1' ust2'.
    enough
      (Hrest : prog_equiv i T1' T2' O1' O2' /\ dteq (TaskDom i) O1' O2').
    {
      simpljoin; splits; eauto.
      destruct_oe_taskd Hoe_d.
      do 2 inv_tuple_rev. 
      unfolds. auto.
    }

    lets Hgctr1: Hgctrl1 HgC1.
    lets Hgstmt1: proj1 Hgctr1.
    assert (HgC2: T2 t = Some (cur_stmt s, ks)).
    {
      Set Printing Implicit.
      unfold code in HTteq. congruence.
      Unset Printing Implicit. 
    }
    lets Hgctr2: Hgctrl2 HgC2.
    lets Hgstmt2: proj1 Hgctr2.
    assert (Hrule_cases:
             head_sat t O1 s /\ head_sat t O2 s /\
               exists q rly guar, deduct_rules t rly guar flt dteq s q). 
    {
      assert (~has_itp ks \/ has_itp ks) by tauto.
      unfold good_stmt in Hgstmt1, Hgstmt2.
      destruct Hgstmt1 as (Hhs1 & Hex1).
      destruct Hgstmt2 as (Hhs2 & _).
      destruct Hex1 as (q & Hor).
      split. auto.
      split. auto.
      exists q.
      destruct Hor; destruct H; simpljoin; tryfalse; do 2 eexists; eauto.
    }
    
    destruct Hrule_cases as (Hhs1 & Hhs2 & q & rly & guar & Hrule).           

    destruct_oe_taskd Hoe_d.
    do 2 inv_tuple_rev. 
    destruct_oe_taskd Hoe_d'.
    do 2 inv_tuple_rev.
    
    lets H__: spec_step2_dteq_preserved Hrule Hinv1 Hinv2 Hhs1 Hhs2.
    lets H_: H__ Hdte Hflt Hdte0. clear H__.
    lets H__: H_ Hsdom1 Hsdom2 Hspstp1 Hspstp2. clear H_.
    lets H_: H__ Hntck1 Hntck2. clear H__.
    destruct H_ as (Heqs' & Heqac' & Hdteq').
    subst s1'. rename s2' into s'.
    subst ac1. rename ac2 into ac_.
    lets Hsdeq1: good_stmt_spec_step_same_dom Hgstmt1 Hinv1 Hspstp1.
    lets Hsdeq2: good_stmt_spec_step_same_dom Hgstmt2 Hinv2 Hspstp2.
    destruct ac; destruct Hac1_cases; destruct Hac2_cases; simpljoin; tryfalse; 
      try (splits; eauto).
    2: { false. apply H0. do 3 eexists; eauto. }
    2: { false. apply H1. do 3 eexists; eauto. }
    {
      eapply prog_equiv_preserved; eauto.
      unfolds.
      introv Hsd1' Hsd2'.
      eapply Hprge; eauto.
      eapply Hsdeq1; eauto.
      eapply Hsdeq2; eauto.        
    } 
    {
      inverts H1.
      rewrite H5 in H2; inverts H2.
      unfolds.
      introv Hsd1' Hsd2'.
      casetac x t0 He Hne.
      - subst.        
        do 2 rewrite upd_task_pool_eq.
        auto.
      -
        casetac t t0 He_ Hne_.
        +
          subst.
          rewrite upd_task_pool_neq; eauto.
          rewrite upd_task_pool_eq.
          rewrite upd_task_pool_neq; eauto.
          rewrite upd_task_pool_eq.
          auto.
        +
          repeat rewrite upd_task_pool_neq; eauto.
          eapply Hprge; eauto.
          eapply Hsdeq1; eauto.
          eapply Hsdeq2; eauto.        
    }

Qed. 

Lemma nflt_ust_equiv:
  forall i i' ust sst' flt, 
    good_flt flt -> 
    ~flt (TaskDom i) (TaskDom i') ->
    ust_equiv i' ust (set ust i sst'). 
Proof.
  introv Hgfl Hnfl.
  unfolds.
  casetac i i' He Hne.
  - subst.
    false. apply Hnfl.
    inverts Hgfl.
    eapply H0; eauto.
  - rewrite neq_set_get; eauto.
Qed. 

Lemma top_rule_good_dteq:
  forall rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) aspc ispc sd, 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd) ->
    good_dteq dteq.
Proof.
  introv Htr.
  inverts Htr.
  auto.
Qed.

Lemma upd_task_pool_prog_equiv:
  forall i i0 T O t C flt, 
    I O -> 
    good_flt flt -> 
    ~ flt (TaskDom i) (TaskDom i0) -> 
    sdom O t i -> 
    prog_equiv i0 T (upd_task_pool T t C) O O. 
Proof.
  introv Hinv Hgflt Hnflt Hsd.
  unfolds.
  introv Hsd_ Hsd'.
  casetac t t0 He Hne.
  - subst.
    lets Hf: sdom_is_fn Hsd Hsd'; eauto.
    subst.
    false.
    apply Hnflt.
    eapply Hgflt; eauto.
  - rewrite upd_task_pool_neq; eauto.
Qed.

Lemma spec_step_dteq:
  forall t sd rly guar flt dteq s q, 
    deduct_rules t rly guar flt dteq s q ->
    good_dteq dteq -> 
    forall i d s' O O' ac_, 
      spec_step sd t s O s' O' ac_ ->
      I O -> 
      head_sat t O s ->
      sdom O t i ->
      ~ flt (TaskDom i) d ->
      ~ (exists cid, ac_ = _TickAct cid) ->
      dteq d O O'. 
Proof.
  introv Hdr.
  induction Hdr; introv Hgd Hss Hinv Hhs Hsdom Hnflt Hntck.
  -
    clear H2.
    simpl in Hhs.
    assert (Hpre1: pre1 t O p).
    { unfolds. split; auto. }
    inverts Hss.
    rename H1 into Hvi.
    specializes Hvi; eauto.
    destruct Hvi as (Hpost1 & (* Hcod &  *)Hsdeq & Hcre & Hobeq).
    auto.
    eapply Hobeq; eauto.
  -
    inverts Hss.
    +
      specializes IHHdr; eauto.
    +
      specializes IHHdr; eauto.
  -
    inverts Hss.
    inverts Hgd.
    eapply gd_equiv_rel; eauto.
  -
    inverts Hss.
    inverts Hgd.
    eapply gd_equiv_rel; eauto.
  -
    inverts Hss.
Qed.

Lemma spec_step_tcre_sdom:
  forall t sd rly guar flt dteq s q, 
    deduct_rules t rly guar flt dteq s q ->
    forall s' O O' t' f arg td, 
      I O ->
      head_sat t O s -> 
      spec_step sd t s O s' O' (_TCreAct t' f arg) ->
      sdom O t td ->
      sdom O t' td. 
Proof.
  introv Hdr.
  induction Hdr; introv Hinv Hhs Hstep Hsd.
  -
    clear H2.
    assert (Hpre1: pre1 t O p).
    { unfolds. split; auto. }
    inverts Hstep.
    rename H1 into Hvi.
    specializes Hvi; eauto.
    simpljoin.
    eapply H3; eauto.
  -
    inverts Hstep; eapply IHHdr; eauto.
  -
    inverts Hstep.
  -
    inverts Hstep.
  -
    inverts Hstep.
Qed. 

Lemma spec_step_ntck_same_cdom:
  forall t sd rly guar flt dteq s q, 
    deduct_rules t rly guar flt dteq s q ->
    forall s' O O' ac, 
      I O ->
      head_sat t O s -> 
      spec_step sd t s O s' O' ac ->
      ~ (exists cid, ac = _TickAct cid) ->
      same_cdom O O'.
Proof. 
  introv Hdr.
  induction Hdr; introv Hinv Hhs Hstep Hntck.
  -
    assert (Hpre1: pre1 t O p).
    { unfolds. split; auto. }
    inverts Hstep.
    specializes H1; eauto.
    (* simpljoin. *)
    (* unfolds. *)
    (* intros. *)
    (* eapply H5; eauto. *)
  -
    inverts Hstep; eapply IHHdr; eauto.
  -
    inverts Hstep.
    apply same_cdom_refl.
  -
    inverts Hstep.
    apply same_cdom_refl.
  -
    inverts Hstep.
Qed.

Lemma nflt_hpstep_d_obsr_equiv:
  forall rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs aspc ispc sd T ust O T' ust' O' act i d
         (Htr : top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) (aspc, ispc, sd))
         (Hgflt : good_flt flt)
         (Hstepd : hpstep_d uprgs (aspc, ispc, sd) (T, ust, O) (T', ust', O') act (TaskDom i))
         (Hnflt : ~ flt (TaskDom i) d)
         (Hinv : I O)
         (Hgctrl : forall (t : tid) (C : code),
             T t = Some C -> good_ctrl t rly_tsk guar_tsk rly_itp guar_itp flt dteq O C), 
    obsr_equiv d dteq (T, ust, O) (T', ust', O'). 
Proof.
  intros. 
  inverts Hstepd.
  rename H10 into Hpstep.
  rename H14 into Hsdom.
  
  lets Hstep_cases: hpstep_inversion Hpstep Hinv Hsdom; eauto.
  specializes Hstep_cases; eauto.
  destruct Hstep_cases as
    [Hustep | [Hcall | [Heni | [Hexapi | [Hexitp | Hspecstep]]]]].

  - (* user step *)
    destruct Hustep as
      (strat & ks & strat_ac & sst & sst' & cid &
         Hact & HTt & Hgetu & Hstrat & Hnex & HT' & Hust' & HO').
    subst.
    unfolds.
    do 6 eexists; splits; eauto.
    destruct d.
    + (* d is task dom *)
      splits.
      * apply prog_equiv_refl.
      * eapply nflt_ust_equiv; eauto.
      * apply ctid_equiv_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto.
        inverts Hgde. eapply gd_equiv_rel; eauto.
    + (* d is SchedDom *)
      splits.
      * apply same_cdom_refl; auto.
      * eapply same_td_for_ct_refl; eauto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.

  - (* call step *)
    destruct Hcall as
      (strat & sst & sst' & f & vl & r & tp & tl & cid &
         Hact & HT & Hgu & Hstrateq & Hgetf & Htvm & HT' & Hust' & HO').
    subst.
    unfolds.
    do 6 eexists; splits; eauto.
    destruct d.
    + (* d is task dom *)
      splits.
      * eapply upd_task_pool_prog_equiv; eauto.
      * eapply nflt_ust_equiv; eauto.
      * apply ctid_equiv_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.
    + (* d is SchedDom *)
      splits.
      * apply same_cdom_refl.
      * apply same_td_for_ct_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.
        
  - (* entering some interrupt handler *)
    destruct Heni as (lev & c & ks & s & cid & Hact & Hispc & HTt & HT' & Hust' & HO').
    subst. 
    unfolds.
    do 6 eexists; splits; eauto.
    destruct d.
    + (* d is task dom *)  
      splits.
      * eapply upd_task_pool_prog_equiv; eauto.
      * apply ust_equiv_refl.
      * apply ctid_equiv_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.
    + (* d is SchedDom *)
      splits.
      * apply same_cdom_refl.
      * apply same_td_for_ct_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.  

  - (* returning from API function *)
    simpljoin.
    unfolds.
    do 6 eexists; splits; eauto.
    destruct d.
    +
      splits.
      * eapply upd_task_pool_prog_equiv; eauto.
      * eapply nflt_ust_equiv; eauto.
      * apply ctid_equiv_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.
    +
      splits.
      * apply same_cdom_refl; auto.
      * apply same_td_for_ct_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.

  - (* exiting from interrupt handler *)
    simpljoin.
    unfolds.
    do 6 eexists; splits ;eauto.
    destruct d.
    +
      splits.
      * eapply upd_task_pool_prog_equiv; eauto.
      * apply ust_equiv_refl; auto.
      * apply ctid_equiv_refl; eauto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.
    +
      splits.
      * apply same_cdom_refl.
      * apply same_td_for_ct_refl; auto.
      * lets Hgde: top_rule_good_dteq Htr; eauto. 
        inverts Hgde. eapply gd_equiv_rel; eauto.

  - (* spec_step *)
    destruct Hspecstep as
      (s & ks & s' & ac_ & cid & Hact & HTt & Hspecstep & Hntck & Hac_or & Hust'). 
    subst.
    assert (Hgctrl__:=Hgctrl).
    specialize (Hgctrl _ _ HTt).
    destruct Hgctrl as (Hgstmt & Hgcont).
    assert (Hrule: head_sat t O s /\ exists q rly guar, deduct_rules t rly guar flt dteq s q).
    {
      destruct Hgstmt as (Hhs & Hex).
      destruct Hex as (q & Hor).
      destruct Hor; simpljoin; (split; [auto | do 3 eexists; eauto ]).
    }
    destruct Hrule as (Hhs & q & rly & guar & Hrule).

    lets Hcte: good_ctrl_hpstep_scd_ctideq Htr Hinv Hgctrl__ Hpstep.
    specializes Hcte; eauto.
    destruct Hcte as (Hstfc & Hcte).
    
    assert (Hgd: good_dteq dteq).
    { inverts Htr; auto. } 
    lets H_: spec_step_dteq Hrule Hgd Hspecstep Hinv Hhs Hsdom.
    specializes H_; eauto.
    rename H_ into Hdteq.
    unfolds.
    do 6 eexists.
    splits; eauto.
    destruct d.
    + (* d is task dom *)
      specialize (Hcte i0).
      enough (Hx: prog_equiv i0 T T' O O').
      {
        simpljoin; splits; eauto.
        apply ust_equiv_refl; auto.
      }
      destruct Hac_or as [Hncre | Hcre].
      *
        simpljoin. subst.
        unfolds.
        introv Hsd0 Hsd0'.
        casetac t t0 He Hne.
        ** subst.
           lets Hieq: sdom_is_fn Hsdom Hsd0; eauto.
           subst.
           false. apply Hnflt.
           eapply Hgflt; eauto.
        **
          rewrite upd_task_pool_neq; eauto.
      *
        destruct Hcre as (t' & f & arg & valstr & strat & Hac_ & Hgf & Hvalstr & HT').
        subst.
        introv Hsd0 Hsd0'.
        casetac t t0 He Hne.
        **
          subst.
          lets Hieq: sdom_is_fn Hsdom Hsd0; eauto.
          subst.
          false. apply Hnflt.
          eapply Hgflt; eauto.          
        **
          (* lets Htne: good_stmt_tcre_neqt Hrule Hhs Hinv Hspecstep. *)
          (* t' must be in the same dom as t *)
          lets Hsdt': spec_step_tcre_sdom Hrule Hinv Hhs Hspecstep Hsdom.
          casetac t0 t' He_ Hne_.
          ***
            subst.
            lets Hieq: sdom_is_fn Hsd0 Hsdt'; eauto.
            subst.
            false. apply Hnflt.
            eapply Hgflt; eauto.
          ***
            rewrite upd_task_pool_neq; eauto.
            rewrite upd_task_pool_neq; eauto.
    +
      splits; eauto.      
      eapply spec_step_ntck_same_cdom; eauto.
Qed. 

Lemma obsr_eq_trans_preserved:
  forall T1 T2 ust1 ust2 O1 O2 T1' T2' ust1' ust2' O1' O2' d dteq, 
    obsr_equiv d dteq (T1, ust1, O1) (T2, ust2, O2) ->
    obsr_equiv d dteq (T1, ust1, O1) (T1', ust1', O1') -> 
    obsr_equiv d dteq (T2, ust2, O2) (T2', ust2', O2') -> 
    good_dteq dteq -> 
    same_td_for_ct O1 O2 -> 
    same_td_for_ct O1 O1' ->       
    I O1 -> I O2 -> I O1' ->  
    obsr_equiv d dteq (T1', ust1', O1') (T2', ust2', O2'). 
Proof.
  introv Hoe12 Hoe11' Hoe22' Hgd Hstd11' Hstd22'.
  introv Hinv1 Hinv2 Hinv1'.    
  assert (Hstfc: same_td_for_ct O1' O1).
  {
    apply same_td_for_ct_sym; auto.
  }
  assert (Hoe1'1: obsr_equiv d dteq (T1', ust1', O1') (T1, ust1, O1)).
  {
    eapply obsr_equiv_sym; eauto.
  }
  assert (Hoe1'2: obsr_equiv d dteq (T1', ust1', O1') (T2, ust2, O2)).
  {
    lets H__: obsr_equiv_trans Hoe1'1 Hoe12; eauto.
  }
  lets H__: obsr_equiv_trans Hoe1'2 Hoe22'; eauto.
  eapply same_td_for_ct_trans; eauto.
Qed. 


Theorem soundness_confidentiality: 
  forall rly_tsk guar_tsk rly_itp guar_itp dteq flt uprgs ospc,
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) ospc ->
    (* good_uprogs uprgs ->  *)
    good_flt flt -> 
    forall (init: sys_config_t -> Prop),
      good_init init -> 
      confidentiality_u flt uprgs ospc init dteq. 
Proof.
  introv Htr (* Hgup *) Hgflt Hgini.
  unfolds.
  introv Hrch1 Hrch2 Hoe_sch Hoe_d Hoe_d' Hstep1 Hstep2.
  destruct ospc as [[aspc ispc] sd].
  destruct cfg1 as [[T1 ust1] O1].
  destruct cfg2 as [[T2 ust2] O2].
  
  lets H1_: rch_good_ctrl Htr Hgini Hrch1; eauto.
  specializes H1_; eauto.
  destruct H1_ as (Hinv1 & Hgctrl1).
  (* lets Hcc1: rch_ct_core Htr Hgini Hrch1; eauto. *)
  (* specializes Hcc1; eauto. *)
  lets Hsuc1: rch_succ_eq Hgini Hrch1; eauto.
  specialize (Hsuc1 (eq_refl _)).

  lets H2_: rch_good_ctrl Htr Hgini Hrch2; eauto.
  specializes H2_; eauto.
  destruct H2_ as (Hinv2 & Hgctrl2).
  (* lets Hcc2: rch_ct_core Htr Hgini Hrch2; eauto. *)
  (* specializes Hcc2; eauto. *)
  lets Hsuc2: rch_succ_eq Hgini Hrch2; eauto.
  specialize (Hsuc2 (eq_refl _)).

  unfolds in Hoe_sch.
  destruct Hoe_sch as
    (T1_ & ust1_ & O1_ & T2_ & ust2_ & O2_ &
       Heq1 & Heq2 & Hsame_cd & Hsame_curd & Hdteq_sch).
  symmetry in Heq1. symmetry in Heq2.
  inverts Heq1. inverts Heq2.

  destruct cfg1' as [[T1' ust1'] O1'].
  destruct cfg2' as [[T2' ust2'] O2'].
  
  assert (Hflt_or: flt d1' d \/ ~flt d1' d) by tauto.
  destruct Hflt_or as [Hflt | Hnflt].

  - (* flt d' d *)
    assert (Hac_or: sched_act ac \/ ~sched_act ac) by tauto.
    destruct Hac_or as [Hschac | Hnschac].
    + (* ac is tick or swi *)
      unfolds in Hschac.
      destruct ac; tryfalse; clear Hschac.
      * (* tick * 2 *)
        unfold obsr_equiv.
        do 6 eexists; splits; eauto.
        destruct d.
        ** (* d is task dom *)
          eapply ticks_preserve_dteq_task_dom; eauto.
        ** (* d is SchedDom *)
          eapply ticks_preserve_dteq_sched_dom; eauto.
      * (* sched * 2 *)
        unfold obsr_equiv.
        do 6 eexists; splits; eauto.
        destruct d.
        ** (* d is task dom *)
          eapply scheds_preserve_dteq_task_dom; eauto.
        ** (* d is SchedDom *)               
          eapply scheds_preserve_dteq_sched_dom; eauto.
    + (* ac is not tick or swi *)
      eapply task_steps_preserve_dteq; eauto.

  - (* ~flt d' d *)
      destruct d1'.
      2: { (* d' is SchedDom --- impossible *) 
        unfolds in Hgflt.
        assert (Hfl: flt SchedDom d).
        {
          eapply Hgflt; eauto.
        }
        false.
      }
      assert (Hac_or: sched_act ac \/ ~sched_act ac) by tauto.
      destruct Hac_or as [Hschac | Hnschac].
      {
        inverts Hstep1.
        unfolds in Hschac.
        destruct ac; tryfalse.
        false.
        apply H12; eexists; eauto.
        false.
        apply H13; eexists; eauto.
      }
      assert (Hd'eq: TaskDom i = d2').
      {
        lets H_: hpstep_d2_same_td Hinv1 Hinv2; eauto.
      }
      subst. 
  
      assert (Hoe11': obsr_equiv d dteq (T1, ust1, O1) (T1', ust1', O1')).
      {
        eapply nflt_hpstep_d_obsr_equiv; eauto.
      }    
      assert (Hoe22': obsr_equiv d dteq (T2, ust2, O2) (T2', ust2', O2')). 
      {
        eapply nflt_hpstep_d_obsr_equiv; eauto.
      }    
      assert (H11': same_td_for_ct O1 O1').
      {
        inverts Hstep1.    
        eapply good_ctrl_hpstep_scd_ctideq; eauto.
      }  
      (* assert (H22': same_td_for_ct O2 O2'). *)
      (* { *)
      (*   inverts Hstep2.     *)
      (*   eapply good_ctrl_hpstep_scd_ctideq; eauto. *)
      (* }   *)
    
      assert (Hinv1': I O1').
      {
        inverts Hstep1.
        lets H__: good_ctrl_sys_step_preserved Htr Hinv1 Hgctrl1 H10; eauto.
        simpljoin; auto.
      }
      assert (Hgdte: good_dteq dteq).
      {
        inverts Htr; auto.
      }
      lets H_: obsr_eq_trans_preserved Hoe_d Hoe11' Hoe22'; eauto.
Qed. 

  
Theorem soundness_integrity : 
  forall rly_tsk guar_tsk rly_itp guar_itp dteq flt uprgs ospc,
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) ospc -> 
    good_flt flt -> 
    forall (init: sys_config_t -> Prop),
      good_init init ->  
      integrity_u flt uprgs ospc init dteq. 
Proof.
  introv Htr Hgflt Hgini.
  unfolds.
  introv Hrch Hstepd Hnflt.
  destruct d'.
  2: { (* d' is SchedDom --- impossible *) 
    unfolds in Hgflt.
    assert (Hfl: flt SchedDom d).
    {
      eapply Hgflt; eauto.
    }
    false.
  }
  (* d' is task dom --- impossible *)
  destruct ospc as [[aspc ispc] sd].
  destruct cfg as [[T ust] O].
  destruct cfg' as [[T' ust'] O'].
  
  lets H_: rch_good_ctrl Htr Hgini Hrch; eauto.
  specializes H_; eauto.
  destruct H_ as (Hinv & Hgctrl).

  eapply nflt_hpstep_d_obsr_equiv; eauto.
Qed. 
  

End Soundness.
