
Require Import LibTactics.
Require Import join_lib.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import rules. 

Require Import specs_common.
Require Import state.
Require Import my_tacs.

Require Import chan_apispecs. 
Require Import sys_spec.

Require Import rly_guar.
Require Import flow_policy.
Require Import obsr_equiv. 

Require Import aux_lemmas.
Require Import inv_props.
Require Import dteq_props.



Lemma chpend_prim_prsv_inv:
  forall vl t O ac vl' O'
         (Hvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpend : chpend_prim t vl O ac (vl', O')),
    I O'.
Proof.
  intros.
  assert (Hinv : I O) by (apply Hpre1).
  clear Hpre1.
  destruct vl as [ | v rest]; simpl in Hvm; tryfalse.
  destruct v; simpl in Hvm; tryfalse.
  destruct rest as [ | v rest].
  2: { simpl in Hvm.
       destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  simpl in Hvm.
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange;
    simpl in Hvm; tryfalse.
  unfold chpend_prim in Hcpend.
  simpl in Hcpend. destruct Hcpend as (Hac0 & Hcpend).
  d_if_hyp.
  - destruct Hcpend as
          (tls & pr & st & m & sus & d & chs & Hgtls & Hgt & Hgchs & Hbody).
      simpl in Hbody.
      destruct (get chs (Z.to_nat (Int.unsigned i))) as [ pc | ] eqn:Eget.
      * destruct pc as [p content]. destruct p as [dsrc ddst]. simpl in Hbody.
        d_if_hyp.
        -- d_mt_hyp.
           ++ simpljoin. subst. exact Hinv.
           ++ d_mt_hyp.
              ** simpljoin. subst. exact Hinv.
              ** simpljoin. subst.
                 change (I_ O) in Hinv.
                 destruct Hinv as
                     [Haf Hdom Hprio Hqaf Hqdom Hmqwt Hwtmq Hchcfg].
                 constructors.
                 --- eapply same_tsks_tsk_active_free_disj with (O:=O); eauto;
                       repeat rew_neq.
                 --- eapply same_tsks_tsk_dom_disj with (O:=O); eauto;
                       repeat rew_neq.
                 --- eapply same_tsks_tsk_diff_id_pr with (O:=O); eauto;
                       repeat rew_neq.
                 --- eapply same_mqs_que_active_free_disj with (O:=O); eauto;
                       repeat rew_neq.
                 --- eapply same_mqs_que_dom_disj with (O:=O); eauto;
                       repeat rew_neq.
                 --- eapply same_tsks_mqs_mq_wt_cond with (O:=O); eauto;
                       repeat rew_neq.
                 --- eapply same_tsks_mqs_wt_mq_cond with (O:=O); eauto;
                       repeat rew_neq.
                 --- unfold chs_sat_config in *.
                     intros chs0 c sd dd content Hchs0 Hgc.
                     rewrite map_get_set in Hchs0.
                     injection Hchs0 as Heqchs0. subst chs0.
                     casetac c (Z.to_nat (Int.unsigned i)) He Hne.
                     +++ subst c. rewrite map_get_set in Hgc. inverts Hgc.
                         specialize (Hchcfg _ _ _ _ _ Hgchs Eget).
                         destruct Hchcfg as [Hsamp | Hqueue].
                         *** destruct Hsamp as ((vv & Hfalse) & Hcfg).
                             inverts Hfalse.
                         *** right. split.
                             { do 2 eexists; reflexivity. }
                             exact (proj2 Hqueue).
                     +++ rewrite neq_set_get in Hgc; auto.
                         eapply Hchcfg; eauto.
        -- simpljoin. subst. exact Hinv.
      * simpljoin. subst. exact Hinv.
  - simpljoin. subst. exact Hinv.
Qed.

Lemma chpend_prim_guar:
  forall vl t O ac vl' O'
         (Hvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpend : chpend_prim t vl O ac (vl', O')),
    guar_tsk_env t O O'.
Proof.
  intros.
  clear Hpre1.
  destruct vl as [ | v rest]; simpl in Hvm; tryfalse.
  destruct v; simpl in Hvm; tryfalse.
  destruct rest as [ | v rest].
  2: { simpl in Hvm.
       destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  simpl in Hvm.
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange;
    simpl in Hvm; tryfalse.
  unfold chpend_prim in Hcpend.
  simpl in Hcpend. destruct Hcpend as (Hac0 & Hcpend).
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  - destruct Hcpend as
        (tls & pr & st & m & sus & d & chs & Hgtls & Hgt & Hgchs & Hbody).
    simpl in Hbody.
    destruct (get chs (Z.to_nat (Int.unsigned i))) as [ pc | ] eqn:Eget.
    + destruct pc as [p content]. destruct p as [dsrc ddst]. simpl in Hbody.
      destruct (Int.eq d ddst) eqn:Edom.
      * destruct content as [msg0 | sz msgs].
        -- simpljoin. subst. apply guar_tsk_refl.
        -- destruct msgs.
           ++ simpljoin. subst. apply guar_tsk_refl.
           ++ simpljoin. subst. unfold guar_tsk_env. split.
              ** intros t0 td Hneq Hsd. unfold sdom_ in *.
                 destruct Hsd as [Ha | Hf].
                 --- left. unfold ex_active_tsk in *; repeat rew_neq.
                 --- right. unfold ex_free_tsk in *; repeat rew_neq.
              ** intros q td Hqsd. unfold q_sdom_ in *.
                 destruct Hqsd as [Ha | Hf].
                 --- left. unfold ex_active_que in *; repeat rew_neq.
                 --- right. unfold ex_free_que in *; repeat rew_neq.
      * simpljoin. subst. apply guar_tsk_refl.
    + simpljoin. subst. apply guar_tsk_refl.
  - simpljoin. subst. apply guar_tsk_refl.
Qed.

Lemma chpend_prim_sdom_iff:
  forall vl t O ac vl' O'
         (Hvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpend : chpend_prim t vl O ac (vl', O')),
    forall t0 td, sdom O t0 td <-> sdom O' t0 td.
Proof.
  intros.
  clear Hpre1.
  destruct vl as [ | v rest]; simpl in Hvm; tryfalse.
  destruct v; simpl in Hvm; tryfalse.
  destruct rest as [ | v rest].
  2: { simpl in Hvm.
       destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  simpl in Hvm.
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange;
    simpl in Hvm; tryfalse.
  unfold chpend_prim in Hcpend.
  simpl in Hcpend. destruct Hcpend as (Hac0 & Hcpend).
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  - destruct Hcpend as
        (tls & pr & st & m & sus & d & chs & Hgtls & Hgt & Hgchs & Hbody).
    simpl in Hbody.
    destruct (get chs (Z.to_nat (Int.unsigned i))) as [ pc | ] eqn:Eget.
    + destruct pc as [p content]. destruct p as [dsrc ddst]. simpl in Hbody.
      destruct (Int.eq d ddst) eqn:Edom.
      * destruct content as [msg0 | sz msgs].
        -- simpljoin. subst. intros; reflexivity.
        -- destruct msgs.
           ++ simpljoin. subst. intros; reflexivity.
           ++ simpljoin. subst. unfold sdom, state, sdom_.
              split; intro Hsd; destruct Hsd as [Ha | Hf].
              ** left. unfold ex_active_tsk in *.
                 destruct Ha as (tls0 & pr0 & st0 & msg0 & sus0 & Htls & Hg).
                 do 5 eexists. split.
                 { repeat rew_neq. }
                 { exact Hg. }
              ** right. unfold ex_free_tsk in *.
                 destruct Hf as (fts & ts & Hfts & Hg & Hin).
                 do 2 eexists. splits.
                 { repeat rew_neq. }
                 { exact Hg. }
                 { exact Hin. }
              ** left. unfold ex_active_tsk in *.
                 destruct Ha as (tls0 & pr0 & st0 & msg0 & sus0 & Htls & Hg).
                 do 5 eexists. split.
                 { repeat rew_neq_in Htls. }
                 { exact Hg. }
              ** right. unfold ex_free_tsk in *.
                 destruct Hf as (fts & ts & Hfts & Hg & Hin).
                 do 2 eexists. splits.
                 { repeat rew_neq_in Hfts. }
                 { exact Hg. }
                 { exact Hin. }
      * simpljoin. subst. intros; reflexivity.
    + simpljoin. subst. intros; reflexivity.
  - simpljoin. subst. intros; reflexivity.
Qed.


Lemma chrecv_ch_update_obsr_equiv_tskd:
  forall O chs td c sd dd content content'
         (Hgchs : get O chlsid = Some (chanlist chs))
         (Hgc : get chs c = Some (sd, dd, content))
         (Hneqd : td <> dd),
    obsr_equiv_tskd td O
      (set O chlsid (chanlist (set chs c (sd, dd, content')))).
Proof.
  intros.
  constructors.
  - eapply obsr_equiv_tasks_nochange; eauto.
    repeat rew_neq.
  - eapply obsr_equiv_mqs_nochange; eauto.
    repeat rew_neq.
  - unfolds.
    rewrite map_get_set.
    split.
    + split; introv Hex; eexists; eauto.
    + introv Hg1 Hg2.
      uni_21_sym (get O chlsid).
      inverts Hg2.
      split.
      * casetac c chid He Hne.
        -- subst chid. rewrite map_get_set.
           split; intros; auto.
           ++ introv Hf. inverts Hf.
           ++ introv Hf.
              unfolds in Hgc. unfolds in Hf. unfold ChanMap in *.
              rewrite Hgc in Hf. inverts Hf.
        -- rew_neq. tauto.
      * introv Hgc1 Hgc2.
        casetac c chid He Hne.
        -- subst. rewrite map_get_set in Hgc2. inverts Hgc2.
           unfolds in Hgc. unfolds in Hgc1. unfold ChanMap in *.
           rewrite Hgc in Hgc1. inverts Hgc1.
           splits; auto. intros; false.
        -- rew_neq_in Hgc2.
           unfolds in Hgc1. unfolds in Hgc2. unfold ChanMap in *.
           rewrite Hgc1 in Hgc2. inverts Hgc2.
           split; try tauto.
  - eapply obsr_equiv_fts_nochange; eauto.
    repeat rew_neq.
  - eapply obsr_equiv_fqs_nochange; eauto.
    repeat rew_neq.
Qed.

Lemma chrecv2_ch_update_obsr_equiv_tskd:
  forall td O1 O2 chs1 chs2 c sd dd content content'
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hgchs1 : get O1 chlsid = Some (chanlist chs1))
         (Hgchs2 : get O2 chlsid = Some (chanlist chs2))
         (Hgc1 : get chs1 c = Some (sd, dd, content))
         (Hgc2 : get chs2 c = Some (sd, dd, content)),
    obsr_equiv_tskd td
      (set O1 chlsid (chanlist (set chs1 c (sd, dd, content'))))
      (set O2 chlsid (chanlist (set chs2 c (sd, dd, content')))).
Proof.
  intros. simpl in Hdte.
  constructors.
  - match goal with H: _ |- _ _ ?O1' ?O2' => set (O1_:=O1'); set (O2_:=O2') end.
    assert (H1 : obsr_equiv_tasks td O1_ O1).
    { eapply obsr_equiv_tasks_nochange; eauto. subst O1_. repeat rew_neq. }
    assert (H2 : obsr_equiv_tasks td O2 O2_).
    { eapply obsr_equiv_tasks_nochange; eauto. subst O2_. repeat rew_neq. }
    eapply dteq_tasks_trans with (O2:=O2); eauto.
    inverts Hdte. eapply dteq_tasks_trans with (O2:=O1); eauto.
  - match goal with H: _ |- _ _ ?O1' ?O2' => set (O1_:=O1'); set (O2_:=O2') end.
    assert (H1 : obsr_equiv_mqs td O1_ O1).
    { eapply obsr_equiv_mqs_nochange; eauto. subst O1_. repeat rew_neq. }
    assert (H2 : obsr_equiv_mqs td O2 O2_).
    { eapply obsr_equiv_mqs_nochange; eauto. subst O2_. repeat rew_neq. }
    eapply dteq_mqs_trans with (O2:=O2); eauto.
    inverts Hdte. eapply dteq_mqs_trans with (O2:=O1); eauto.
  - unfolds. do 2 rewrite map_get_set. split.
    + split; intros; eexists; eauto.
    + introv Hg1 Hg2. inverts Hg1. inverts Hg2.
      casetac c chid He Hne.
      * subst. do 2 rewrite map_get_set. split; try tauto.
        introv Hg1' Hg2'. rewrite map_get_set in Hg1'.
        rewrite map_get_set in Hg2'. inverts Hg1'. inverts Hg2'.
        splits; eauto.
      * do 4 rew_neq. inverts Hdte.
        unfolds in oe_td_chs.
        destruct oe_td_chs as (_ & Hall).
        eapply Hall; eauto.
  - match goal with H: _ |- _ _ ?O1' ?O2' => set (O1_:=O1'); set (O2_:=O2') end.
    assert (H1 : obsr_equiv_freetids td O1_ O1).
    { eapply obsr_equiv_fts_nochange; eauto. subst O1_. repeat rew_neq. }
    assert (H2 : obsr_equiv_freetids td O2 O2_).
    { eapply obsr_equiv_fts_nochange; eauto. subst O2_. repeat rew_neq. }
    eapply dteq_fts_trans with (O2:=O2); eauto.
    inverts Hdte. eapply dteq_fts_trans with (O2:=O1); eauto.
  - match goal with H: _ |- _ _ ?O1' ?O2' => set (O1_:=O1'); set (O2_:=O2') end.
    assert (H1 : obsr_equiv_freeqids td O1_ O1).
    { eapply obsr_equiv_fqs_nochange; eauto. subst O1_. repeat rew_neq. }
    assert (H2 : obsr_equiv_freeqids td O2 O2_).
    { eapply obsr_equiv_fqs_nochange; eauto. subst O2_. repeat rew_neq. }
    eapply dteq_fqs_trans with (O2:=O2); eauto.
    inverts Hdte. eapply dteq_fqs_trans with (O2:=O1); eauto.
Qed.

Lemma chpend_prim_integrity_oblig:
  forall vl t O ac vl' O' td d
         (Hvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpend : chpend_prim t vl O ac (vl', O'))
         (Hnex : ~ (exists cid, ac = _TickAct cid))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d),
    obsr_equiv_data d O O'.
Proof.
  intros. clear Hnex.
  destruct vl as [ | v rest]; simpl in Hvm; tryfalse.
  destruct v; simpl in Hvm; tryfalse.
  destruct rest as [ | v rest].
  2: { simpl in Hvm.
       destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  simpl in Hvm.
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange;
    simpl in Hvm; tryfalse.
  unfold chpend_prim in Hcpend. simpl in Hcpend.
  destruct Hcpend as (Hac & Hcpend).
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  - destruct Hcpend as
        (tls & pr & st & m & sus & td0 & chs & Hgtls & Hgt & Hgchs & Hbody).
    simpl in Hbody.
    destruct (get chs (Z.to_nat (Int.unsigned i))) as [pc | ] eqn:Eget.
    + destruct pc as [p content]. destruct p as [sd dd]. simpl in Hbody.
      destruct (Int.eq td0 dd) eqn:Edom.
      * destruct content as [msg | sz msgs].
        -- simpljoin. subst. apply obsr_equiv_data_refl.
        -- destruct msgs as [ | msg msgs].
           ++ simpljoin. subst. apply obsr_equiv_data_refl.
           ++ simpljoin. subst.
              assert (Htd0 : td0 = td).
              { eapply tls_sdom_td_eq; eauto. apply Hpre1. }
              assert (Hdd : td0 = dd).
              { casetac td0 dd He Hne; auto.
                rewrite Int.eq_false in Edom; auto. tryfalse. }
              subst td0. subst dd.
              destruct d.
              ** simpl.
                 assert (Hneqd : i0 <> td).
                 { intro Heq. subst i0. apply Hnfl. constructors. }
                 eapply chrecv_ch_update_obsr_equiv_tskd; eauto.
              ** constructors; try rew_neq.
      * simpljoin. subst. apply obsr_equiv_data_refl.
    + simpljoin. subst. apply obsr_equiv_data_refl.
  - simpljoin. subst. apply obsr_equiv_data_refl.
Qed.

Lemma chpend_prim_confidentiality_oblig:
  forall vl t O1 O2 ac1 ac2 vl1' vl2' O1' O2' td
         (Hvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre2 : pre2 t O1 O2 trivial_asrt td obsr_equiv_data flows_to)
         (Hcpend1 : chpend_prim t vl O1 ac1 (vl1', O1'))
         (Hcpend2 : chpend_prim t vl O2 ac2 (vl2', O2'))
         (Hnex1 : ~ (exists cid, ac1 = _TickAct cid))
         (Hnex2 : ~ (exists cid, ac2 = _TickAct cid)),
    obsr_equiv_data (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'.
Proof.
  intros. clear Hnex1 Hnex2.
  des_pre2 Hpre2.
  destruct vl as [ | v rest]; simpl in Hvm; tryfalse.
  destruct v; simpl in Hvm; tryfalse.
  destruct rest as [ | v rest].
  2: { simpl in Hvm.
       destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  simpl in Hvm.
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange;
    simpl in Hvm; tryfalse.
  unfold chpend_prim in Hcpend1, Hcpend2. simpl in Hcpend1, Hcpend2.
  destruct Hcpend1 as (Hac1 & Hcpend1).
  destruct Hcpend2 as (Hac2 & Hcpend2). subst ac1. subst ac2.
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  2: { simpljoin. subst. splits; auto. }
  destruct Hcpend1 as
      (tls1 & pr1 & st1 & m1 & sus1 & d1 & chs1 & Hgtls1 & Hgt1 & Hgchs1 & Hbody1).
  destruct Hcpend2 as
      (tls2 & pr2 & st2 & m2 & sus2 & d2 & chs2 & Hgtls2 & Hgt2 & Hgchs2 & Hbody2).
  assert (Hd1 : d1 = td').
  { eapply tls_sdom_td_eq; [apply Hpre11 | exact Hgtls1 | exact Hgt1 | exact Hsd1]. }
  assert (Hd2 : d2 = td').
  { eapply tls_sdom_td_eq; [apply Hpre12 | exact Hgtls2 | exact Hgt2 | exact Hsd2]. }
  subst d1. subst d2.
  remember (Z.to_nat (Int.unsigned i)) as c. clear Heqc.
  assert (Hsome : get chs1 c <> None <-> get chs2 c <> None).
  { simpl in Hdte'. inverts Hdte'.
    unfolds in oe_td_chs. destruct oe_td_chs as (_ & Hall).
    specialize (Hall chs1 chs2 c Hgchs1 Hgchs2). tauto. }
  destruct (get chs1 c) as [pc1 | ] eqn:Eget1;
    destruct (get chs2 c) as [pc2 | ] eqn:Eget2.
  - destruct pc1 as [p1 content1]. destruct p1 as [sd1 dd1].
    destruct pc2 as [p2 content2]. destruct p2 as [sd2 dd2].
    assert (Hch : sd1 = sd2 /\ dd1 = dd2 /\ (dd1 = td' -> content1 = content2)).
    { simpl in Hdte'. inverts Hdte'. unfolds in oe_td_chs.
      destruct oe_td_chs as (_ & Hall).
      specialize (Hall chs1 chs2 c Hgchs1 Hgchs2).
      destruct Hall as (_ & Hall). eapply Hall; eauto. }
    destruct Hch as (Hsdch & Hddch & Hcontent). subst sd1. subst dd1.
    simpl in Hbody1, Hbody2.
    destruct (Int.eq td' dd2) eqn:Edom.
    + assert (Hdd : dd2 = td').
      { casetac dd2 td' He Hne; auto.
        rewrite Int.eq_false in Edom; auto. tryfalse. }
      assert (Hceq : content1 = content2) by (apply Hcontent; auto).
      subst content1. rename content2 into content.
      destruct content as [msg | sz msgs].
      * simpljoin. subst. splits; auto.
      * destruct msgs as [ | msg msgs].
        -- simpljoin. subst. splits; auto.
        -- simpljoin. subst. splits; auto.
           simpl. eapply chrecv2_ch_update_obsr_equiv_tskd; eauto.
    + simpljoin. subst. splits; auto.
  - exfalso.
    assert (Hne : Some pc1 <> None) by discriminate.
    apply (proj1 Hsome) in Hne. apply Hne. reflexivity.
  - exfalso.
    assert (Hne : Some pc2 <> None) by discriminate.
    apply (proj2 Hsome) in Hne. apply Hne. reflexivity.
  - simpl in Hbody1, Hbody2. simpljoin. subst. splits; auto.
Qed.



Lemma dr_chanrecv:
  forall vl t, 
    tl_vl_match (Tint8 :: nil) vl = true -> 
    deduct_rules t (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (chan_apispecs.chan_recv vl) q_star. 
Proof.
  introv Hvm.
  constructors.
  - apply stable_pre_trivial_asrt.
  - introv Hpre1 Hcpend.
    splits.
    + splits.
      * unfolds; auto.
      * eapply chpend_prim_prsv_inv; eauto. 
      * eapply chpend_prim_guar; eauto.
    +
      eapply chpend_prim_sdom_iff; eauto.
    +
      introv Hf.
      unfolds in Hcpend.
      repeat (d_mt_hyp; simpljoin; tryfalse).
    +
      (* integrity oblig. *)
      introv Hnex Hsd Hnfl.
      eapply chpend_prim_integrity_oblig; eauto.
  -
    (* confidentiality oblig. *)
    introv Hpre2 Hcpend1 Hcpend2 Hnex1 Hnex2.
    eapply chpend_prim_confidentiality_oblig; eauto.

Qed.

