
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

Require Import int_auto.

Lemma chan_flow_false:
  forall O sd dd chs c content, 
    I O -> 
    ~ flows_to (TaskDom sd) (TaskDom dd) ->
    get O chlsid = Some (chanlist chs) ->
    get chs c = Some (sd, dd, content) ->
    False.
Proof.
  introv Hinv Hnfl Hgchs Hgc.
  inverts Hinv.
  unfolds in inv_chcfg.
  lets H_: inv_chcfg Hgchs Hgc.
  clear inv_chcfg.
  apply Hnfl.
  assert (exists ctp, get chcfg c = Some (sd, dd, ctp)).
  {
    destruct H_; simpljoin; eexists; eauto.
  }
  simpljoin.
  eapply flt_chs; eauto.
Qed.   





Lemma chs_content_update_prsv_inv:
  forall O chs cid sd dd old_content new_content,
    I O ->
    get O chlsid = Some (chanlist chs) ->
    get chs cid = Some (sd, dd, old_content) ->
    ((exists vold vnew,
        old_content = SampleCh vold /\ new_content = SampleCh vnew) \/
     (exists szold msold sznew msnew,
        old_content = QueueCh szold msold /\
        new_content = QueueCh sznew msnew)) ->
    I (set O chlsid (chanlist (set chs cid (sd, dd, new_content)))).
Proof.
  intros.
  change (I_ O) in H.
  destruct H as [Haf Hdom Hprio Hqaf Hqdom Hmqwt Hwtmq Hchcfg].
  constructors.
  - eapply same_tsks_tsk_active_free_disj with (O:=O); eauto;
      repeat rew_neq.
  - eapply same_tsks_tsk_dom_disj with (O:=O); eauto;
      repeat rew_neq.
  - eapply same_tsks_tsk_diff_id_pr with (O:=O); eauto;
      repeat rew_neq.
  - eapply same_mqs_que_active_free_disj with (O:=O); eauto;
      repeat rew_neq.
  - eapply same_mqs_que_dom_disj with (O:=O); eauto;
      repeat rew_neq.
  - eapply same_tsks_mqs_mq_wt_cond with (O:=O); eauto;
      repeat rew_neq.
  - eapply same_tsks_mqs_wt_mq_cond with (O:=O); eauto;
      repeat rew_neq.
  - unfold chs_sat_config in *.
    intros chs0 c sd0 dd0 content Hchs0 Hgc.
    rewrite map_get_set in Hchs0.
    injection Hchs0 as Heqchs0. subst chs0.
    casetac c cid He Hne.
    + subst c. rewrite map_get_set in Hgc. inverts Hgc.
      specialize (Hchcfg _ _ _ _ _ H0 H1).
      destruct H2 as [Hsamp | Hqueue].
      * destruct Hsamp as (vold & vnew & Hold & Hnew).
        subst old_content. inverts Hnew.
        destruct Hchcfg as [Hcfg | Hfalse].
        -- left. split.
           ++ eexists; reflexivity.
           ++ exact (proj2 Hcfg).
        -- destruct Hfalse as ((sz & ms & Hfalse) & Hcfg).
           inverts Hfalse.
      * destruct Hqueue as (szold & msold & sznew & msnew & Hold & Hnew).
        subst old_content. inverts Hnew.
        destruct Hchcfg as [Hfalse | Hcfg].
        -- destruct Hfalse as ((v & Hfalse) & Hcfg). inverts Hfalse.
        -- right. split.
           ++ do 2 eexists; reflexivity.
           ++ exact (proj2 Hcfg).
    + rewrite neq_set_get in Hgc; auto.
      eapply Hchcfg; eauto.
Qed.

Lemma chpost_prim_prsv_inv:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: Tptr Tvoid :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpost : chpost_prim t vl O ac (vl', O')),
    I O'.
Proof.
  intros.
  assert (Hinv : I O) by (apply Hpre1).
  clear Hpre1.
  destruct vl as [ | v rest]; simpl in Htvm; tryfalse.
  destruct v; simpl in Htvm; tryfalse.
  destruct rest as [ | vmsg rest].
  { simpl in Htvm.
    destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange.
  2: { simpl in Htvm; discriminate. }
  destruct rest as [ | v rest].
  2: { unfold chpost_prim in Hcpost. simpl in Hcpost.
       simpljoin. subst. exact Hinv. }
  destruct vmsg.
  { simpl in Htvm; discriminate. }
  { unfold chpost_prim in Hcpost. simpl in Hcpost.
    destruct Hcpost as (Hac0 & Hcpost).
    destruct (negb (Int.lt i Int.zero)); simpljoin; subst; exact Hinv. }
  { simpl in Htvm; discriminate. }
  simpl in Htvm.
  simpl in Htvm.
  unfold chpost_prim in Hcpost.
  simpl in Hcpost. destruct Hcpost as (Hac0 & Hcpost).
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  - destruct Hcpost as
        (tls & pr & st & m0 & sus & d & chs & Hgtls & Hgt & Hgchs & Hbody).
    simpl in Hbody.
    destruct (get chs (Z.to_nat (Int.unsigned i))) as [ pc | ] eqn:Eget.
    + destruct pc as [p content]. destruct p as [dsrc ddst]. simpl in Hbody.
      destruct (negb (Int.eq dsrc ddst)) eqn:Ediff.
      * destruct (Int.eq d dsrc) eqn:Edom.
        -- destruct content as [vold | sz ms].
           ++ simpljoin. subst.
              eapply chs_content_update_prsv_inv; eauto.
           ++ destruct (Nat.ltb (length ms) sz) eqn:Eroom.
              ** simpljoin. subst.
                 eapply chs_content_update_prsv_inv; eauto.
                 right. do 4 eexists; split; reflexivity.
              ** simpljoin. subst. exact Hinv.
        -- simpljoin. subst. exact Hinv.
      * simpljoin. subst. exact Hinv.
    + simpljoin. subst. exact Hinv.
  - simpljoin. subst. exact Hinv.
Qed.

Lemma chls_update_guar:
  forall t O chs,
    guar_tsk_env t O (set O chlsid (chanlist chs)).
Proof.
  intros. unfold guar_tsk_env. split.
  - intros t0 td Hneq Hsd. unfold sdom_ in *.
    destruct Hsd as [Ha | Hf].
    + left. unfold ex_active_tsk in *; repeat rew_neq.
    + right. unfold ex_free_tsk in *; repeat rew_neq.
  - intros q td Hqsd. unfold q_sdom_ in *.
    destruct Hqsd as [Ha | Hf].
    + left. unfold ex_active_que in *; repeat rew_neq.
    + right. unfold ex_free_que in *; repeat rew_neq.
Qed.

Lemma chpost_prim_guar:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: Tptr Tvoid :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpost : chpost_prim t vl O ac (vl', O')),
    guar_tsk_env t O O'.
Proof.
  intros. clear Hpre1.
  destruct vl as [ | v rest]; simpl in Htvm; tryfalse.
  destruct v; simpl in Htvm; tryfalse.
  destruct rest as [ | vmsg rest].
  { simpl in Htvm.
    destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange.
  2: { simpl in Htvm; discriminate. }
  destruct rest as [ | v rest].
  2: { unfold chpost_prim in Hcpost. simpl in Hcpost.
       simpljoin. subst. apply guar_tsk_refl. }
  destruct vmsg.
  { simpl in Htvm; discriminate. }
  { unfold chpost_prim in Hcpost. simpl in Hcpost.
    destruct Hcpost as (Hac0 & Hcpost).
    destruct (negb (Int.lt i Int.zero)); simpljoin; subst;
      apply guar_tsk_refl. }
  { simpl in Htvm; discriminate. }
  simpl in Htvm.
  unfold chpost_prim in Hcpost.
  simpl in Hcpost. destruct Hcpost as (Hac0 & Hcpost).
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  - destruct Hcpost as
        (tls & pr & st & m0 & sus & d & chs & Hgtls & Hgt & Hgchs & Hbody).
    simpl in Hbody.
    destruct (get chs (Z.to_nat (Int.unsigned i))) as [ pc | ] eqn:Eget.
    + destruct pc as [p content]. destruct p as [dsrc ddst]. simpl in Hbody.
      destruct (negb (Int.eq dsrc ddst)) eqn:Ediff.
      * destruct (Int.eq d dsrc) eqn:Edom.
        -- destruct content as [vold | sz ms].
           ++ simpljoin. subst. apply chls_update_guar.
           ++ destruct (Nat.ltb (length ms) sz) eqn:Eroom.
              ** simpljoin. subst. apply chls_update_guar.
              ** simpljoin. subst. apply guar_tsk_refl.
        -- simpljoin. subst. apply guar_tsk_refl.
      * simpljoin. subst. apply guar_tsk_refl.
    + simpljoin. subst. apply guar_tsk_refl.
  - simpljoin. subst. apply guar_tsk_refl.
Qed.

Lemma chls_update_sdom_iff:
  forall O chs t0 td,
    sdom O t0 td <-> sdom (set O chlsid (chanlist chs)) t0 td.
Proof.
  intros. unfold sdom, state, sdom_. split; intro Hsd;
    destruct Hsd as [Ha | Hf].
  - left. unfold ex_active_tsk in *.
    destruct Ha as (tls & pr & st & msg & sus & Htls & Hg).
    do 5 eexists. split.
    + repeat rew_neq.
    + exact Hg.
  - right. unfold ex_free_tsk in *.
    destruct Hf as (fts & ts & Hfts & Hg & Hin).
    do 2 eexists. splits.
    + repeat rew_neq.
    + exact Hg.
    + exact Hin.
  - left. unfold ex_active_tsk in *.
    destruct Ha as (tls & pr & st & msg & sus & Htls & Hg).
    do 5 eexists. split.
    + repeat rew_neq_in Htls.
    + exact Hg.
  - right. unfold ex_free_tsk in *.
    destruct Hf as (fts & ts & Hfts & Hg & Hin).
    do 2 eexists. splits.
    + repeat rew_neq_in Hfts.
    + exact Hg.
    + exact Hin.
Qed.

Lemma chpost_prim_sdom_iff:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: Tptr Tvoid :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpost : chpost_prim t vl O ac (vl', O')),
    forall t0 td, sdom O t0 td <-> sdom O' t0 td.
Proof.
  intros. clear Hpre1.
  destruct vl as [ | v rest]; simpl in Htvm; tryfalse.
  destruct v; simpl in Htvm; tryfalse.
  destruct rest as [ | vmsg rest].
  { simpl in Htvm.
    destruct (Int.unsigned i <=? Byte.max_unsigned); discriminate. }
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn:Hrange.
  2: { simpl in Htvm; discriminate. }
  destruct rest as [ | v rest].
  2: { unfold chpost_prim in Hcpost. simpl in Hcpost.
       simpljoin. subst. intros; reflexivity. }
  destruct vmsg.
  { simpl in Htvm; discriminate. }
  { unfold chpost_prim in Hcpost. simpl in Hcpost.
    destruct Hcpost as (Hac0 & Hcpost).
    destruct (negb (Int.lt i Int.zero)); simpljoin; subst;
      intros; reflexivity. }
  { simpl in Htvm; discriminate. }
  simpl in Htvm.
  unfold chpost_prim in Hcpost.
  simpl in Hcpost. destruct Hcpost as (Hac0 & Hcpost).
  destruct (negb (Int.lt i Int.zero)) eqn:Echid.
  - destruct Hcpost as
        (tls & pr & st & m0 & sus & d & chs & Hgtls & Hgt & Hgchs & Hbody).
    simpl in Hbody.
    destruct (get chs (Z.to_nat (Int.unsigned i))) as [ pc | ] eqn:Eget.
    + destruct pc as [p content]. destruct p as [dsrc ddst]. simpl in Hbody.
      destruct (negb (Int.eq dsrc ddst)) eqn:Ediff.
      * destruct (Int.eq d dsrc) eqn:Edom.
        -- destruct content as [vold | sz ms].
           ++ simpljoin. subst. apply chls_update_sdom_iff.
           ++ destruct (Nat.ltb (length ms) sz) eqn:Eroom.
              ** simpljoin. subst. apply chls_update_sdom_iff.
              ** simpljoin. subst. intros; reflexivity.
        -- simpljoin. subst. intros; reflexivity.
      * simpljoin. subst. intros; reflexivity.
    + simpljoin. subst. intros; reflexivity.
  - simpljoin. subst. intros; reflexivity.
Qed.






Lemma chsend_obsr_equiv_tskd':
  forall t O tls pr st m sus sd dd chs td c content content'
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, st, m, sus, sd))
         (Hgchs : get O chlsid = Some (chanlist chs))
         (Hgc : get chs c = Some (sd, dd, content))
         (Hsd : sdom O t sd)
         (Hneqchd: sd <> dd)
         (Hneqd : td <> dd), 
    obsr_equiv_tskd td O (set O chlsid (chanlist (set chs c (sd, dd, content')))).  
Proof. 
  intros. 
  constructors.
  -
    eapply obsr_equiv_tasks_nochange; eauto.
    repeat rew_neq.
  -
    eapply obsr_equiv_mqs_nochange; eauto.
    repeat rew_neq.
  -
    unfolds.
    rewrite map_get_set.
    split.
    +
      split.
      * 
        introv Hex; eexists; eauto.
      *
        introv Hex; eexists; eauto.
    +
      introv Hg1 Hg2.
      uni_21_sym (get O chlsid).
      inverts Hg2.
      split. 
      * 
        casetac c chid He Hne.
        ** subst chid.
           rewrite map_get_set.
           split; intros; auto.
           *** introv Hf. inverts Hf.
           *** introv Hf.
               unfolds in Hgc. unfolds in Hf.
               unfold ChanMap in *.
               rewrite Hgc in Hf.
               inverts Hf.
        **
          rew_neq.
          tauto.
      *
        introv Hgc1 Hgc2.
        casetac c chid He Hne.
        **
          subst.
          rewrite map_get_set in Hgc2.
          inverts Hgc2.
          unfolds in Hgc. unfolds in Hgc1.
          unfold ChanMap in *.
          rewrite Hgc in Hgc1.
          inverts Hgc1.
          splits; auto.
          {
            intros. false. 
          }          
            
        **
          rew_neq_in Hgc2.
          unfolds in Hgc1. unfolds in Hgc2.
          unfold ChanMap in *.
          rewrite Hgc1 in Hgc2.
          inverts Hgc2.
          split; try tauto.
  -
    eapply obsr_equiv_fts_nochange; eauto.
    repeat rew_neq.
  -    
    eapply obsr_equiv_fqs_nochange; eauto.
    repeat rew_neq.
Qed. 
               
Lemma chsend_obsr_equiv_tskd:
  forall t O tls pr st m sus sd dd chs c td content content'
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, st, m, sus, sd))
         (Hgchs : get O chlsid = Some (chanlist chs))
         (Hgc : get chs c = Some (sd, dd, content))
         (Hsd : sdom O t sd)
         (Hneqd : sd <> td)
         (Hneqchd: sd <> dd)
         (Hnfl : ~ flows_to (TaskDom sd) (TaskDom td)), 
    obsr_equiv_tskd td O (set O chlsid (chanlist (set chs c (sd, dd, content')))).  
Proof.
  intros.
  casetac td dd He Hf.
  - subst.
    false.
    eapply chan_flow_false; eauto.
    apply Hpre1.
  - 
    eapply chsend_obsr_equiv_tskd'; eauto.
Qed. 

(* Lemma queuing_send_obsr_equiv_tskd': *)
(*   forall t O tls pr st m sus sd dd td chs c s v a  *)
(*          (Hpre1 : pre1 t O trivial_asrt) *)
(*          (Hgtls : get O abstcblsid = Some (abstcblist tls)) *)
(*          (Hgt : get tls t = Some (pr, st, m, sus, sd)) *)
(*          (Hgchs : get O chlsid = Some (chanlist chs)) *)
(*          (Hgc : get chs c = Some (sd, dd, QueueCh s v)) *)
(*          (Hsd : sdom O t sd) *)
(*          (Hneqchd : sd <> dd) *)
(*          (Hneqd: td <> dd),  *)

(*     obsr_equiv_tskd td  O *)
(*       (set O chlsid *)
(*          (chanlist *)
(*             (set chs c (sd, dd, QueueCh s (v ++ Vptr a :: nil))))). *)
(* Proof. *)
(*   intros. *)
(*   constructors. *)
(*   - *)
(*     eapply obsr_equiv_tasks_nochange; eauto. *)
(*     repeat rew_neq. *)
(*   - *)
(*     eapply obsr_equiv_mqs_nochange; eauto. *)
(*     repeat rew_neq. *)
(*   - *)
(*     unfolds. *)
(*     rewrite map_get_set. *)
(*     split. *)
(*     + *)
(*       split. *)
(*       * introv Hchls. eexists; eauto. *)
(*       * introv Hex. eexists; eauto. *)
(*     + *)
(*       introv Hg1 Hg2. *)
(*       inverts Hg2. *)
(*       casetac c chid He Hne. *)
(*       * subst. *)
(*         rewrite map_get_set. *)
(*         split. *)
(*         ** *)
(*           split; intros. *)
(*           *** introv Hf; tryfalse. *)
(*           *** *)
(*             introv Hn. *)
(*             uni_12 (get O chlsid). *)
(*             unfolds in Hgc. unfolds in Hn. *)
(*             unfold ChanMap in *. *)
(*             uni_12 (ChanMod.get chs1 chid). *)
(*         ** *)
(*           introv Hgc1 Hgc2. *)
(*           rewrite map_get_set in Hgc2. *)
(*           inverts Hgc2. *)
(*           unfolds in Hgc. unfolds in Hgc1. *)
(*           unfold ChanMap in *. *)
(*           uni_12 (get O chlsid). *)
(*           uni_12 (ChanMod.get chs1 chid). *)
(*           splits; auto. *)
(*           intros. *)
(*           false.  *)
(*       * *)
(*         repeat rew_neq. *)
(*         uni_12 (get O chlsid). *)
(*         split; try tauto. *)
(*         introv Hg1 Hg2. *)
(*         unfolds in Hg1. unfolds in Hg2. *)
(*         unfold ChanMap in *. *)
(*         uni_12 (ChanMod.get chs1 chid). *)
(*         split; try tauto. *)
(*   - *)
(*     eapply obsr_equiv_fts_nochange; eauto. *)
(*     repeat rew_neq. *)
(*   - *)
(*     eapply obsr_equiv_fqs_nochange; eauto. *)
(*     repeat rew_neq. *)

(* Qed.    *)

(* Lemma queuing_send_obsr_equiv_tskd: *)
(*   forall t O tls pr st m sus sd dd td chs c s v a  *)
(*          (Hpre1 : pre1 t O trivial_asrt) *)
(*          (Hgtls : get O abstcblsid = Some (abstcblist tls)) *)
(*          (Hgt : get tls t = Some (pr, st, m, sus, sd)) *)
(*          (Hgchs : get O chlsid = Some (chanlist chs)) *)
(*          (Hgc : get chs c = Some (sd, dd, QueueCh s v)) *)
(*          (Hnfl : ~ flows_to (TaskDom sd) (TaskDom td)) *)
(*          (Hsd : sdom O t sd) *)
(*          (Hneqchd : sd <> dd) *)
(*          (Hneqd: sd <> td),  *)

(*     obsr_equiv_tskd td  O *)
(*       (set O chlsid *)
(*          (chanlist *)
(*             (set chs c (sd, dd, QueueCh s (v ++ Vptr a :: nil))))). *)

(* Proof. *)
(*   intros. *)
(*   casetac td dd He Hne. *)
(*   - subst. *)
(*     false.  *)
(*     eapply chan_flow_false; eauto. *)
(*     apply Hpre1. *)
(*   - clear Hneqd. *)
(*     eapply queuing_send_obsr_equiv_tskd'; eauto. *)
(* Qed.      *)
   
Lemma chpost_prim_integrity_oblig:
  forall vl t O ac vl' O' td d
         (Htvm : tl_vl_match (Tint8 :: Tptr Tvoid :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Hcpost : chpost_prim t vl O ac (vl', O'))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d), 
    obsr_equiv_data d O O'. 
Proof.
  intros.

  unfolds in Hcpost.
  do 4 (d_mt_hyp; simpljoin; simpl in Htvm; tryfalse;
        try (simpl; apply obsr_equiv_data_refl; fail)).
  d_if_hyp; try (simpljoin; simpl in Htvm; tryfalse; fail).
  2: { simpljoin. apply obsr_equiv_data_refl. }
  do 2 (d_mt_hyp; try (simpljoin; simpl in Htvm; tryfalse; fail)).
  - simpljoin. apply obsr_equiv_data_refl.
  - match goal with
      H: exists _, _ |- _ =>
        destruct H as (tls & pr & st & m & sus & d_ & chs & Hgtls & Hgt & Hgchs & Hmt)
    end.
    d_mt_hyp.
    2: { simpljoin. apply obsr_equiv_data_refl. }
    
    destruct p as (dsd & content).
    destruct dsd as (sd & dd).
    do 2 (d_if_hyp; try (simpljoin; apply obsr_equiv_data_refl)).
    assert (Hneqchd: sd <> dd).
    {
      casetac sd dd He Hne; auto.
      subst. 
      rewrite Int.eq_true in E3.
      simpl in E3; false.
    }
    subst.
    clear E3.
    assert (d_ = sd).
    {
      casetac d_ sd He Hne; auto.
      rewrite Int.eq_false in E4; auto.
      false.
    }
    subst.
    clear E4.
    assert (sd = td).
    {
      eapply tls_sdom_td_eq; eauto.
      apply Hpre1.
    }
    subst td.
    
    d_mt_hyp.
    + (* send to sampling channel *)
      destruct Hmt as (HO' & Hvl'); subst. 
      destruct d.
      *
        simpl.
        assert (Hneqd: sd <> i0).
        {
          casetac sd i0 He Hne; auto.
          subst.
          false.
          apply Hnfl; constructors.
        }
        rename i0 into td.      
        eapply chsend_obsr_equiv_tskd; eauto.
      *
        constructors; try rew_neq.
    +
      d_if_hyp.
      2: { simpljoin. apply obsr_equiv_data_refl; eauto. }

      (* send to queuing channel *)
      destruct Hmt as (HO' & Hvl').
      subst.
      destruct d.
      * 
        simpl.
        assert (Hneqd: sd <> i0).
        {
          casetac sd i0 He Hne; auto.
          subst.
          false.
          apply Hnfl; constructors.
        }
        rename i0 into td.      
        eapply chsend_obsr_equiv_tskd; eauto.
      *
        constructors; try rew_neq.

Qed.



Lemma obsr_equiv_chan_doms_eq:      
  forall td O1 O2 chs1 chs2 sd1 sd2 dd1 dd2 content1 content2 c, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 chlsid = Some (chanlist chs1) ->
    get O2 chlsid = Some (chanlist chs2) ->
    get chs1 c = Some (sd1, dd1, content1) -> 
    get chs2 c = Some (sd2, dd2, content2) ->
    (sd1 = sd2 /\ dd1 = dd2). 
Proof.
  introv Hoe Hgchs1 Hgchs2 Hgc1 Hgc2.
  simpl in Hoe.
  inverts Hoe.
  unfolds in oe_td_chs.
  destruct oe_td_chs as (Heqv & Hall).
  specialize (Hall chs1 chs2 c Hgchs1 Hgchs2).
  destruct Hall as (Heqv_ & Hall).
  specializes Hall; eauto.
  simpljoin. splits; eauto.
Qed.

Lemma obsr_equiv_chan_content_eq:     
  forall td O1 O2 chs1 chs2 sd1 sd2 dd1 dd2 content1 content2 c, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 chlsid = Some (chanlist chs1) ->
    get O2 chlsid = Some (chanlist chs2) ->
    get chs1 c = Some (sd1, dd1, content1) -> 
    get chs2 c = Some (sd2, dd2, content2) ->
    dd1 = td ->
    content1 = content2. 
Proof.
  introv Hoe Hgchs1 Hgchs2 Hgc1 Hgc2 Hde.
  simpl in Hoe.
  inverts Hoe.
  unfolds in oe_td_chs.
  destruct oe_td_chs as (Heqv & Hall).
  specialize (Hall chs1 chs2 c Hgchs1 Hgchs2).
  destruct Hall as (Heqv_ & Hall).
  specializes Hall; eauto.
  simpljoin.
  eauto.
Qed. 

Lemma chsend2_obsr_equiv_tskd_prsv:
  forall t O1 O2 sd dd tls1 tls2 pr1 st1 m1 sus1 pr2 st2 m2 sus2 chs1 chs2 content content' c
         (Hpre11 : pre1 t O1 trivial_asrt)
         (Hpre12 : pre1 t O2 trivial_asrt)
         (Hdte : obsr_equiv_data (TaskDom dd) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom sd) O1 O2)
         (Hflt : flows_to (TaskDom sd) (TaskDom dd))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr1, st1, m1, sus1, sd))
         (Hgchs1 : get O1 chlsid = Some (chanlist chs1))
         (Ec1 : get chs1 c = Some (sd, dd, content))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr2, st2, m2, sus2, sd))
         (Hgchs2 : get O2 chlsid = Some (chanlist chs2))
         (Ec2 : get chs2 c = Some (sd, dd, content)) 
         (Hsd1 : sdom O1 t sd)
         (Hsd2 : sdom O2 t sd)
         (Hneqchd : sd <> dd), 
    obsr_equiv_tskd dd (set O1 chlsid (chanlist (set chs1 c (sd, dd, content'))))
      (set O2 chlsid (chanlist (set chs2 c (sd, dd, content')))).
Proof.
  intros.
  constructors.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_tasks dd O1_ O1).
    {
      eapply obsr_equiv_tasks_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_tasks dd O2 O2_).
    {
      eapply obsr_equiv_tasks_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_tasks_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_tasks_trans with (O2:=O1); eauto.    
  - 
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_mqs dd O1_ O1).
    {
      eapply obsr_equiv_mqs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_mqs dd O2 O2_).
    {
      eapply obsr_equiv_mqs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_mqs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_mqs_trans with (O2:=O1); eauto.
  -
    unfolds.
    do 2 rewrite map_get_set.
    split.
    + split; intros;
        eexists; eauto.
    +
      introv Hg1 Hg2.
      inverts Hg1. 
      inverts Hg2.
      casetac c chid He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split; try tauto.
        introv Hg1_ Hg2_.
        rewrite map_get_set in Hg1_.
        rewrite map_get_set in Hg2_.
        inverts Hg1_. inverts Hg2_.
        splits; eauto.
      *
        do 4 rew_neq.
        split.
        **
          eapply Hdte; eauto.
        **
          introv Hg1_ Hg2_.
          lets Heq_: obsr_equiv_chan_doms_eq Hdte Hgchs1 Hgchs2.
          specializes Heq_; eauto.
          simpljoin; splits; auto.
          introv Hdd.
          subst.
          simpl in Hdte.
          inverts Hdte.
          unfolds in oe_td_chs.
          destruct oe_td_chs as (_ & Hall).
          lets H_: Hall chid Hgchs1 Hgchs2.
          destruct H_ as (_ & Hall_).
          specializes Hall_; eauto.
          simpljoin; eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_freetids dd O1_ O1).
    {
      eapply obsr_equiv_fts_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_freetids dd O2 O2_).
    {
      eapply obsr_equiv_fts_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_fts_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_fts_trans with (O2:=O1); eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_freeqids dd O1_ O1).
    {
      eapply obsr_equiv_fqs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_freeqids dd O2 O2_).
    {
      eapply obsr_equiv_fqs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_fqs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_fqs_trans with (O2:=O1); eauto.
Qed. 

Lemma chpost_prim_confidentiality_oblig:
  forall vl t O1 O2 ac1 ac2 vl1' vl2' O1' O2' td
         (Htvm : tl_vl_match (Tint8 :: Tptr Tvoid :: nil) vl = true)
         (Hpre2 : pre2 t O1 O2 trivial_asrt td obsr_equiv_data flows_to)
         (Hcpost1 : chpost_prim t vl O1 ac1 (vl1', O1'))
         (Hcpost2 : chpost_prim t vl O2 ac2 (vl2', O2')), 
    obsr_equiv_data (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'.  
Proof.
  intros.
  des_pre2 Hpre2.
  simpl.
  unfolds in Hcpost1; unfolds in Hcpost2.
  do 4 (d_mt_hyp; 
        try (simpl in Hcpost1; simpl in Hcpost2; simpljoin; splits; auto; fail)).
  destruct Hcpost1 as (Hac1 & Hif1).
  destruct Hcpost2 as (Hac2 & Hif2).
  subst ac1. subst ac2.
  d_if_hyp.
  2: { simpljoin. splits; auto. } 
  d_mt_hyp; try (simpljoin; splits; auto; fail).
  destruct Hif1 as (tls1 & pr1 & st1 & m1 & sus1 & d1_ & chs1 & Hgtls1 & Hgt1 & Hgchs1 & Hmt1).
  destruct Hif2 as (tls2 & pr2 & st2 & m2 & sus2 & d2_ & chs2 & Hgtls2 & Hgt2 & Hgchs2 & Hmt2).
  remember (Z.to_nat (Int.unsigned i)) as c.
  clear Heqc.
  assert (Hgceq: get chs1 c <> None <-> get chs2 c <> None).
  {
    eapply Hdte; eauto.
  }
  destruct (get chs1 c) eqn: Ec1;
    destruct (get chs2 c) eqn: Ec2; tryfalse. 
  -
    clear Hgceq.
    destruct p as (dsd1 & content1).
    destruct dsd1 as (sd1 & dd1).
    destruct p0 as (dsd2 & content2).
    destruct dsd2 as (sd2 & dd2).
    assert (Heq2: sd1 = sd2 /\ dd1 = dd2).
    {
      eapply obsr_equiv_chan_doms_eq; eauto.
    }
    destruct Heq2 as (Hsdeq & Hddeq).
    subst sd1 dd1.
    rename sd2 into sd.
    rename dd2 into dd.
    d_if_hyp; try (simpljoin; splits; eauto; fail).
    assert (d1_ = td').
    {
      eapply tls_sdom_td_eq with (O:=O1); eauto.
      apply Hpre11.
    }
    subst d1_.
    assert (d2_ = td').
    {
      eapply tls_sdom_td_eq with (O:=O2); eauto.
      apply Hpre12.
    }
    subst d2_.
    assert (Hneqchd: sd <> dd).
    {
      casetac sd dd He Hne; auto.
      subst. 
      rewrite Int.eq_true in E5.
      simpl in E5; false.
    }
    d_if_hyp; try (simpljoin; splits; eauto; fail).
    assert (td' = sd).
    {
      casetac td' sd He Hne; eauto.
      rewrite Int.eq_false in E6; eauto.
      false.
    }
    subst td'.
    casetac td dd He Hf.
    + (* td = dd *)
      subst.
      assert (content1 = content2).
      {
        eapply obsr_equiv_chan_content_eq with (td:=dd); eauto.
      }
      subst content1. rename content2 into content.
      destruct content eqn: Ecnt.
      * simpljoin.
        splits; auto.
        eapply chsend2_obsr_equiv_tskd_prsv; eauto.
      * d_if_hyp; try (simpljoin; splits; eauto; fail).
        simpljoin.
        splits; auto.
        eapply chsend2_obsr_equiv_tskd_prsv; eauto.
        
    + (* td <> dd *)
      destruct content1 eqn: Ecnt1;
        destruct content2 eqn: Ecnt2;
        simpljoin; splits; eauto.
      *
        lets H1_: chsend_obsr_equiv_tskd' Hpre11 Hgtls1 Hgt1 Hgchs1 Ec1 Hsd1.
        lets H11': H1_ Hneqchd Hf. clear H1_.
        lets H2_: chsend_obsr_equiv_tskd' Hpre12 Hgtls2 Hgt2 Hgchs2 Ec2 Hsd2.
        lets H22': H2_ Hneqchd Hf. clear H2_.
        apply obsr_equiv_tskd_sym in H11'.      
        eapply obsr_equiv_tskd_trans with (O2:=O2); eauto.
        eapply obsr_equiv_tskd_trans with (O2:=O1); eauto.
      *
        d_if_hyp; simpljoin.
        **
          lets H1_: chsend_obsr_equiv_tskd' Hpre11 Hgtls1 Hgt1 Hgchs1 Ec1 Hsd1.
          lets H11': H1_ Hneqchd Hf. 
          lets H2_: chsend_obsr_equiv_tskd' Hpre12 Hgtls2 Hgt2 Hgchs2 Ec2 Hsd2.
          lets H22': H2_ Hneqchd Hf.
          apply obsr_equiv_tskd_sym in H11'.      
          eapply obsr_equiv_tskd_trans with (O2:=O2); eauto.
          eapply obsr_equiv_tskd_trans with (O2:=O1); eauto.
        **
          lets H1_: chsend_obsr_equiv_tskd' Hpre11 Hgtls1 Hgt1 Hgchs1 Ec1 Hsd1.
          lets H11': H1_ Hneqchd Hf.
          apply obsr_equiv_tskd_sym in H11'.                
          eapply obsr_equiv_tskd_trans with (O2:=O1); eauto.
      *
        d_if_hyp; simpljoin. 
      *
        d_if_hyp; simpljoin.
        **
          lets H1_: chsend_obsr_equiv_tskd' Hpre11 Hgtls1 Hgt1 Hgchs1 Ec1 Hsd1.
          lets H11': H1_ Hneqchd Hf. clear H1_.
          lets H2_: chsend_obsr_equiv_tskd' Hpre12 Hgtls2 Hgt2 Hgchs2 Ec2 Hsd2.
          lets H22': H2_ Hneqchd Hf. clear H2_.
          apply obsr_equiv_tskd_sym in H11'.      
          eapply obsr_equiv_tskd_trans with (O2:=O2); eauto.
          eapply obsr_equiv_tskd_trans with (O2:=O1); eauto.
        **
          lets H2_: chsend_obsr_equiv_tskd' Hpre12 Hgtls2 Hgt2 Hgchs2 Ec2 Hsd2.
          lets H22': H2_ Hneqchd Hf.
          eapply obsr_equiv_tskd_trans with (O2:=O2); eauto.
      *
        d_if_hyp; simpljoin.
      *
        d_if_hyp; d_if_hyp; simpljoin; auto.
        **
          lets H1_: chsend_obsr_equiv_tskd' Hpre11 Hgtls1 Hgt1 Hgchs1 Ec1 Hsd1.
          lets H11': H1_ Hneqchd Hf. clear H1_.
          lets H2_: chsend_obsr_equiv_tskd' Hpre12 Hgtls2 Hgt2 Hgchs2 Ec2 Hsd2.
          lets H22': H2_ Hneqchd Hf. clear H2_.
          apply obsr_equiv_tskd_sym in H11'.      
          eapply obsr_equiv_tskd_trans with (O2:=O2); eauto.
          eapply obsr_equiv_tskd_trans with (O2:=O1); eauto.
        **
          lets H2_: chsend_obsr_equiv_tskd' Hpre12 Hgtls2 Hgt2 Hgchs2 Ec2 Hsd2.
          lets H22': H2_ Hneqchd Hf.
          eapply obsr_equiv_tskd_trans with (O2:=O2); eauto.
        **
          lets H1_: chsend_obsr_equiv_tskd' Hpre11 Hgtls1 Hgt1 Hgchs1 Ec1 Hsd1.
          lets H11': H1_ Hneqchd Hf.
          apply obsr_equiv_tskd_sym in H11'.                
          eapply obsr_equiv_tskd_trans with (O2:=O1); eauto.
      *
        d_if_hyp; d_if_hyp; simpljoin; auto.
  -
    false.
    assert (Hne: Some p <> None) by (introv Hf; inverts Hf).
    apply Hgceq in Hne.
    apply Hne; auto.
  -
    false.
    assert (Hne: Some p <> None) by (introv Hf; inverts Hf).
    apply Hgceq in Hne.
    apply Hne; auto.
  -
    clear Hgceq.
    simpljoin.
    splits; auto.
Qed.     

Lemma dr_chansend: 
  forall vl t, 
    tl_vl_match (Tint8 :: Tptr Tvoid :: nil) vl = true -> 
    deduct_rules t get_hprio_in_dom (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (chan_apispecs.chan_send vl) q_star. 
Proof.
  introv Htvm.
  constructors.
  - apply stable_pre_trivial_asrt.
  - introv Hpre1 Hcpost.
    splits.
    + splits.
      * unfolds; auto.
      * eapply chpost_prim_prsv_inv; eauto. 
      * eapply chpost_prim_guar; eauto.  
    +eapply chpost_prim_sdom_iff; eauto.
    + introv Hf.
      unfolds in Hcpost.
      repeat (d_mt_hyp; simpljoin; tryfalse).
    +
      (* integrity oblig. *) 
      introv Hnex Hsd Hnfl.
      eapply chpost_prim_integrity_oblig; eauto.
  -
    (* confidentiality oblig. *)
    introv Hpre2 Hcpost1 Hcpost2 Hnex1 Hnex2.

    Set Nested Proofs Allowed. 

    eapply chpost_prim_confidentiality_oblig; eauto.
Qed. 

