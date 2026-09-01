
Require Import LibTactics.
Require Import join_lib.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import rules. 

Require Import specs_common.
Require Import state.
Require Import my_tacs.

Require Import mq_apispecs. 
Require Import sys_spec.

Require Import rly_guar.
Require Import flow_policy.
Require Import obsr_equiv. 

Require Import aux_lemmas.
Require Import inv_props.
Require Import dteq_props.

Definition qpost_before_schd_post (vl: vallist) (t: tid) (vl': vallist) (O: osabst) :=   
  (exists z, vl' = Vint32 (Int.repr z) :: nil).  


Lemma qpost_nowt_obsr_equiv_mqs:
  forall t O qid m qls ms sz tdq td i
         (Hpre1 : pre1 t O (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq ms sz nil, tdq))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) (TaskDom i)),
    obsr_equiv_mqs i O
      (set O quelsid (absecblist (set qls qid (msgq (ms ++ Vptr m :: nil) sz nil, tdq)))).
Proof.
  intros.
  unfolds.
  lets H_: tq_same_dom_qdom Hpre1 Hsd Hgqls Hgq.
  subst tdq.
  assert (Hneqd: td <> i).
  {
    casetac td i He Hne; auto.
    false. apply Hnfl. subst. constructors. 
  }
  
  split.
  - rewrite map_get_set. 
    split; intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    rewrite map_get_set in Hg2.
    inverts Hg2.
    split.
    +
      unfold ex_mq_in_dom.
      uni_12_sym (get O quelsid).
      casetac qid q He Hne.
      * subst.
        rewrite map_get_set.
        split.
        ** introv Hex.
           destruct Hex as (ms_ & sz_ & ts & Hgq_).
           Set Printing Implicit.
           unfold qid in Hgq_.
           rewrite Hgq in Hgq_.
           inverts Hgq_.
           Unset Printing Implicit.
           false.
        ** introv Hex.
           simpljoin.
           inverts H.
           do 3 eexists; eauto.
      *
        rew_neq.
        tauto.
    +
      introv Hgq1 Hgq2 Hd.
      subst d1.
      casetac qid q He Hne.
      * subst.
        rewrite map_get_set in Hgq2.
        inverts Hgq2.
        rewrite Hgqls in Hg1.
        symmetry in Hg1.
        inverts Hg1.
        Set Printing Implicit.
        unfold qid in Hgq1.
        rewrite Hgq1 in Hgq.
        inverts Hgq.
        Unset Printing Implicit.
        false. 
      *
        rew_neq_in Hgq2.
        rewrite Hgqls in Hg1. inverts Hg1.
        Set Printing Implicit.
        unfold Modules.qid in Hgq1.
        rewrite Hgq1 in Hgq2.
        inverts Hgq2.
        Unset Printing Implicit.
        auto.
Qed.            

Lemma qpost_integrity_oblig1:
  forall t O qid m qls ms sz tdq td d 
         (Hpre1 : pre1 t O (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq ms sz nil, tdq))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d), 
    obsr_equiv_data d O
      (set O quelsid (absecblist (set qls qid (msgq (ms ++ Vptr m :: nil) sz nil, tdq)))). 
Proof.
  intros.
  unfolds.
  destruct d.
  - constructors.
    + eapply obsr_equiv_tasks_nochange with (O1:=O); eauto.
      rew_neq.
    + eapply qpost_nowt_obsr_equiv_mqs; eauto.
    + eapply obsr_equiv_chs_nochange with (O1:=O); eauto.
      rew_neq.
    + eapply obsr_equiv_fts_nochange with (O1:=O); eauto.
      rew_neq.
    + eapply obsr_equiv_fqs_nochange with (O1:=O); eauto.
      rew_neq.
  - constructors; try (repeat rew_neq; fail).
Qed. 

Lemma qpost_wt_obsr_equiv_tasks: 
  forall O qls qid ms sz ts td0 i tls t' pr st msg sus pr' st' msg' sus' 
         (Hinv: I O)
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq ms sz ts, td0))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt' : get tls t' = Some (pr, st, msg, sus, td0))
         (Hneqd : td0 <> i), 
    obsr_equiv_tasks i O
      (set (set O abstcblsid (abstcblist (set tls t' (pr', st', msg', sus', td0)))) 
         quelsid (absecblist (set qls qid (msgq ms sz (remove_tid t' ts), td0)))). 
Proof.
  intros.
  unfolds.
  splits.
  - rew_neq.
    rewrite map_get_set.
    split.
    + intros; eexists; eauto.
    + introv Hex. destruct Hex as (tls0 & Heq). inverts Heq.
      eexists; eauto.
  - introv Hgq1 Hgq2.
    rew_neq_in Hgq2.
    rewrite map_get_set in Hgq2.
    inverts Hgq2.
    uni_12_sym (get O abstcblsid).
    split.
    +
      unfold ex_tsk_in_dom.
      casetac t' t He Hne.
      * subst.
        rewrite map_get_set. 
        split.
        ** introv Hex.
           rewrite Hgt' in Hex.
           simpljoin. inverts H.
           do 4 eexists; eauto.
        ** introv Hex. simpljoin.
           inverts H.
           do 4 eexists; eauto.
      *
        rew_neq.
        tauto.
    +
      introv Hg1 Hg2 Hd.
      subst d1.
      casetac t' t He Hne.
      * subst.
        rewrite map_get_set in Hg2.
        inverts Hg2.
        rewrite Hgt' in Hg1.
        inverts Hg1.
        false.
      * rew_neq_in Hg2.
        rewrite Hg1 in Hg2.
        inverts Hg2.
        splits; eauto.
Qed. 

Lemma qpost_wt_obsr_equiv_mqs: 
  forall O qls qid ms sz ts td0 i tls t' pr st msg sus pr' st' msg' sus' 
         (Hinv: I O)
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq ms sz ts, td0))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt' : get tls t' = Some (pr, st, msg, sus, td0))
         (Hneqd : td0 <> i), 
    obsr_equiv_mqs i O
      (set (set O abstcblsid (abstcblist (set tls t' (pr', st', msg', sus', td0)))) 
         quelsid (absecblist (set qls qid (msgq ms sz (remove_tid t' ts), td0)))). 
Proof.
  intros.
  unfolds.
  splits.
  - 
    rewrite map_get_set.
    split.
    + intros; eexists; eauto.
    + introv Hex. destruct Hex as (tls0 & Heq). inverts Heq.
      eexists; eauto.
  -
    introv Hgq1 Hgq2.
    rewrite map_get_set in Hgq2.
    inverts Hgq2.
    uni_12_sym (get O quelsid).
    split.
    + unfold ex_mq_in_dom.
      casetac qid q He Hne.
      * subst.
        rewrite map_get_set.
        split; introv Hex.
        **
          destruct Hex as (ms_ & sz_ & ts_ & Hgq_).
          Set Printing Implicit.
          unfold qid in Hgq_. unfold tid in Hgq.
          rewrite Hgq in Hgq_.
          Unset Printing Implicit.
          symmetry in Hgq_.
          inverts Hgq_.
          false.
        **
          simpljoin.
          inverts H.
          false.
      *
        rew_neq.
        tauto.
    +
      introv Hg1 Hg2 Hd.
      subst d1.
      casetac qid q He Hne.
      * subst. rewrite map_get_set in Hg2.
        inverts Hg2.
        Set Printing Implicit.
        unfold qid in Hg1. unfold tid in Hgq.
        rewrite Hgq in Hg1.
        Unset Printing Implicit.
        inverts Hg1.
        false.
      * rew_neq_in Hg2.
        Set Printing Implicit.
        unfold Modules.qid in Hg1.
        unfold tid in Hg2. 
        rewrite Hg1 in Hg2.
        inverts Hg2.
        Unset Printing Implicit.
        auto.
Qed.

Lemma qpost_integrity_oblig2:
  forall t O qid m qls ms sz t0 l tdq td td0 d t' p st m0 sus tls
         (Hpre1 : pre1 t O (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq ms sz (t0 :: l), tdq))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hghwt : GetHWait tls (t0 :: l) t')
         (Hgt' : get tls t' = Some (p, st, m0, sus, td))
         (Hsd : sdom O t td0)
         (Hnfl : ~ flows_to (TaskDom td0) d), 
    obsr_equiv_data d O
      (set (set O abstcblsid (abstcblist (set tls t' (p, rdy, Vptr m, sus, td)))) quelsid
         (absecblist (set qls qid (msgq ms sz (remove_tid t' (t0 :: l)), tdq)))). 
Proof.
  intros.
  unfolds.
  destruct d.
  -
    lets H_: tq_same_dom_qdom Hpre1 Hsd Hgqls Hgq.
    subst tdq.
    assert (Hneqd: td0 <> i).
    {
      casetac td0 i He Hne; auto.
      false. apply Hnfl. subst. constructors. 
    }
    assert (Hpre1_ := Hpre1).
    destruct Hpre1 as (Hp1 & Hinv).
    inverts Hinv.
    destruct Hghwt as (Hin & Hrem).
    clear Hrem.
    unfolds in inv_mq_wt.
    lets H_: inv_mq_wt Hgqls Hgtls Hgq Hin.
    destruct H_ as (pr_ & msg_ & sus_ & to_ & Hgt'_).
    rewrite Hgt' in Hgt'_.
    inverts Hgt'_.

    clear inv_mq_wt.

    constructors.
    +
      eapply qpost_wt_obsr_equiv_tasks; eauto.
      apply Hpre1_.
    + 
      eapply qpost_wt_obsr_equiv_mqs; eauto.
      apply Hpre1_.
      
    + eapply obsr_equiv_chs_nochange with (O1:=O); eauto.
      repeat rew_neq.

    + eapply obsr_equiv_fts_nochange with (O1:=O); eauto.
      repeat rew_neq.

    + eapply obsr_equiv_fqs_nochange with (O1:=O); eauto.
      repeat rew_neq.
  -
    constructors;
      repeat rew_neq.
Qed.                      

Lemma qpost2_nowt_obsr_equiv_mqs:
  forall t O1 O2 qid m td td' qls1 qls2 ms sz 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hsd1 : sdom O1 t td')
         (Hsd2 : sdom O2 t td')
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgq1 : get qls1 qid = Some (msgq ms sz nil, td'))
         (Hgq2 : get qls2 qid = Some (msgq ms sz nil, td')), 
    obsr_equiv_mqs td
      (set O1 quelsid (absecblist (set qls1 qid (msgq (ms ++ Vptr m :: nil) sz nil, td'))))
      (set O2 quelsid (absecblist (set qls2 qid (msgq (ms ++ Vptr m :: nil) sz nil, td')))). 
Proof.
  intros.
  unfolds.
  split.
  - do 2 rewrite map_get_set.
    split.
    + introv Hex. eexists; eauto.
    + introv Hex. eexists; eauto.
  - introv Hg1 Hg2.
    rewrite map_get_set in Hg1.
    rewrite map_get_set in Hg2.
    symmetry in Hg1. inverts Hg1.
    symmetry in Hg2. inverts Hg2.
    split.
    + unfold ex_mq_in_dom.
      casetac qid q He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split; introv Hex.
        ** destruct Hex as (ms_ & sz_ & ts & Heq).
           inverts Heq.
           do 3 eexists; eauto.
        ** destruct Hex as (ms_ & sz_ & ts_ & Heq).
           inverts Heq.
           do 3 eexists; eauto.
      *
        do 2 rew_neq.
        eapply dte_ex_mq_in_dom_same with (td:=td); eauto.
    +
      introv Hg1 Hg2 Htd.
      subst d1.
      casetac qid q He Hne.
      * subst.
        rewrite map_get_set in Hg1, Hg2.
        inverts Hg1.
        inverts Hg2.
        auto.
      * rew_neq_in Hg1.
        rew_neq_in Hg2.
        lets H_: dte_ex_mq_in_dom_same q Hdte Hgqls1 Hgqls2.
        assert (Hex: exists ms sz ts, get qls1 q = Some (msgq ms sz ts, td)).
        { destruct mq1. do 3 eexists; eauto. }
        apply H_ in Hex.
        destruct Hex as (ms2 & sz2 & ts2 & Hgq2_).
        Set Printing Implicit.
        unfold tid in Hgq2_.
        rewrite Hg2 in Hgq2_.
        inverts Hgq2.
        Unset Printing Implicit.
        inverts Hgq2_.
        simpl in Hdte.
        inverts Hdte.
        eapply oe_td_mqs; eauto.
Qed.         

Lemma qpost2_nowt_obsr_equiv_tskd:
  forall t O1 O2 qid m td td' qls1 qls2 ms sz 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hsd1 : sdom O1 t td')
         (Hsd2 : sdom O2 t td')
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgq1 : get qls1 qid = Some (msgq ms sz nil, td'))
         (Hgq2 : get qls2 qid = Some (msgq ms sz nil, td')), 
    obsr_equiv_tskd td
      (set O1 quelsid (absecblist (set qls1 qid (msgq (ms ++ Vptr m :: nil) sz nil, td'))))
      (set O2 quelsid (absecblist (set qls2 qid (msgq (ms ++ Vptr m :: nil) sz nil, td')))). 
Proof.
  intros.
  constructors.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_tasks td O1_ O1).
    {
      eapply obsr_equiv_tasks_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_tasks td O2 O2_).
    {
      eapply obsr_equiv_tasks_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_tasks_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_tasks_trans with (O2:=O1); eauto.
  -
    eapply qpost2_nowt_obsr_equiv_mqs; eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_chans td O1_ O1).
    {
      eapply obsr_equiv_chs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_chans td O2 O2_).
    {
      eapply obsr_equiv_chs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_chs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_chs_trans with (O2:=O1); eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_freetids td O1_ O1).
    {
      eapply obsr_equiv_fts_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_freetids td O2 O2_).
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
    assert (H1_1: obsr_equiv_freeqids td O1_ O1).
    {
      eapply obsr_equiv_fqs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_freeqids td O2 O2_).
    {
      eapply obsr_equiv_fqs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_fqs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_fqs_trans with (O2:=O1); eauto.
Qed. 

Lemma qpost2_obsr_equiv_tasks:
  forall t O1 O2 qid m td td' qls1 qls2 tls1 tls2 p1 st1 m1 sus1 p2 st2 m2 sus2 ms sz ts t'
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))            
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (* (Hin_ts1 : In t1' (t0 :: ts)) *)
         (* (Hin_ts2 : In t2' (t0 :: ts)) *)
         (Hgt1' : get tls1 t' = Some (p1, st1, m1, sus1, td'))
         (Hgt2' : get tls2 t' = Some (p2, st2, m2, sus2, td')), 

    obsr_equiv_tasks td
      (set (set O1 abstcblsid (abstcblist (set tls1 t' (p1, rdy, Vptr m, sus1, td'))))
         quelsid (absecblist (set qls1 qid (msgq ms sz (remove_tid t' ts), td'))))
      (set (set O2 abstcblsid (abstcblist (set tls2 t' (p2, rdy, Vptr m, sus2, td'))))
         quelsid (absecblist (set qls2 qid (msgq ms sz (remove_tid t' ts), td')))). 
Proof.
  intros.
  unfolds.
  splits.
  -
    rew_neq. rewrite map_get_set.
    rew_neq. rewrite map_get_set.
    split; intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    rew_neq_in Hg1.
    rew_neq_in Hg2.
    rewrite map_get_set in Hg1.
    rewrite map_get_set in Hg2.
    inverts Hg1.
    inverts Hg2.

    split .
    +
      unfold ex_tsk_in_dom.
      casetac t' t0 He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split.
        ** introv Hex.
           destruct Hex as (pr & st & m_ & sus & Heq).
           inverts Heq. 
           do 4 eexists; eauto.
        ** introv Hex.
           destruct Hex as (pr & st & m_ & sus & Heq).
           inverts Heq.
           do 4 eexists; eauto.
      *
        do 2 rew_neq.
        eapply dte_ex_tsk_in_dom_same; eauto.
    +
      introv Hg1 Hg2 Hd.
      casetac t' t0 He Hne.
      * subst.
        rewrite map_get_set in Hg1.
        rewrite map_get_set in Hg2.
        inverts Hg1. inverts Hg2.
        rename d2 into td.
        lets H_: obsr_equiv_data_tsk_eq Hdte Hgtls1 Hgtls2 Hgt1' Hgt2'.
        simpljoin; splits; eauto.
      *
        rew_neq_in Hg1.
        rew_neq_in Hg2.
        subst d1.
        lets H_: dte_ex_tsk_in_dom_same t0 Hdte Hgtls1 Hgtls2.
        assert (Hex: exists pr0 st m sus0, get tls1 t0 = Some (pr0, st, m, sus0, td)).
        {
          do 4 eexists; eauto.
        }
        apply H_ in Hex.
        destruct Hex as (pr2_ & st2_ & m2_ & sus2_ & Hgt2).
        Set Printing Implicit.
        unfold msg in Hgt2.
        rewrite Hg2 in Hgt2.
        inverts Hgt2.
        Unset Printing Implicit.
        clear H_.
        lets H_: obsr_equiv_data_tsk_eq Hdte Hgtls1 Hgtls2; eauto.
Qed. 

Lemma qpost2_obsr_equiv_mqs: 
  forall t O1 O2 qid m td td' qls1 qls2 tls1 tls2 p1 sus1 p2 sus2 ms sz ts t' 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))            
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (* (Hin_ts1 : In t1' (t0 :: ts)) *)
         (* (Hin_ts2 : In t2' (t0 :: ts)) *)
         (Hgq1 : get qls1 qid = Some (msgq ms sz ts, td'))
         (Hgq2 : get qls2 qid = Some (msgq ms sz ts, td')), 

    obsr_equiv_mqs td
      (set (set O1 abstcblsid (abstcblist (set tls1 t' (p1, rdy, Vptr m, sus1, td'))))
         quelsid (absecblist (set qls1 qid (msgq ms sz (remove_tid t' ts), td'))))
      (set (set O2 abstcblsid (abstcblist (set tls2 t' (p2, rdy, Vptr m, sus2, td'))))
         quelsid (absecblist (set qls2 qid (msgq ms sz (remove_tid t' ts), td')))). 
Proof.
  intros.
  unfolds.
  split.
  -  do 2 rewrite map_get_set.
     split; intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    rewrite map_get_set in Hg1.
    rewrite map_get_set in Hg2.
    inverts Hg1.
    inverts Hg2.
    split.
    + unfold ex_mq_in_dom.
      casetac qid q He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split.
        ** introv Hex.
           destruct Hex as (ms_ & sz_ & ts_ & Heq).
           inverts Heq.
           do 3 eexists; eauto.
        ** introv Hex.
           destruct Hex as (ms_ & sz_ & ts_ & Heq).
           inverts Heq.
           do 3 eexists; eauto.
      *
        do 2 rew_neq.
        eapply dte_ex_mq_in_dom_same; eauto.
    +
      introv Hg1 Hg2 Hd.
      casetac qid q He Hne.
      * subst. rewrite map_get_set in Hg1. rewrite map_get_set in Hg2.
        inverts Hg1. inverts Hg2.
        auto.
      * rew_neq_in Hg1.
        rew_neq_in Hg2.
        subst d1.
        lets H_: dte_ex_mq_in_dom_same q Hdte Hgqls1 Hgqls2.
        assert (Hex: exists ms sz ts, get qls1 q = Some (msgq ms sz ts, td)).
        {
          destruct mq1.
          do 3 eexists; eauto.
        }
        apply H_ in Hex.
        destruct Hex as (ms_ & sz_ & ts_ & Hgq2_).
        Set Printing Implicit.
        unfold tid in Hgq2_.
        rewrite Hg2 in Hgq2_.
        symmetry in Hgq2_.
        inverts Hgq2_.
        Unset Printing Implicit.
        clear H_.
        rename d2 into td.
        simpl in Hdte.
        eapply Hdte; eauto.
Qed.         

Lemma qpost2_obsr_equiv_tskd: 
  forall t O1 O2 qid m td td' qls1 qls2 tls1 tls2 p1 st1 m1 sus1 p2 st2 m2 sus2 ms sz ts t' 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))            
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)))
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (* (Hin_ts1 : In t1' (t0 :: ts)) *)
         (* (Hin_ts2 : In t2' (t0 :: ts)) *)
         (Hgt1' : get tls1 t' = Some (p1, st1, m1, sus1, td'))
         (Hgt2' : get tls2 t' = Some (p2, st2, m2, sus2, td'))
         (Hgq1 : get qls1 qid = Some (msgq ms sz ts, td'))
         (Hgq2 : get qls2 qid = Some (msgq ms sz ts, td')), 

    obsr_equiv_tskd td
      (set (set O1 abstcblsid (abstcblist (set tls1 t' (p1, rdy, Vptr m, sus1, td'))))
         quelsid (absecblist (set qls1 qid (msgq ms sz (remove_tid t' ts), td'))))
      (set (set O2 abstcblsid (abstcblist (set tls2 t' (p2, rdy, Vptr m, sus2, td'))))
         quelsid (absecblist (set qls2 qid (msgq ms sz (remove_tid t' ts), td')))). 
Proof.
  intros.
  constructors.
  - 
    eapply qpost2_obsr_equiv_tasks; eauto.
  -
    eapply qpost2_obsr_equiv_mqs; eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_chans td O1_ O1).
    {
      eapply obsr_equiv_chs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_chans td O2 O2_).
    {
      eapply obsr_equiv_chs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_chs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_chs_trans with (O2:=O1); eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_freetids td O1_ O1).
    {
      eapply obsr_equiv_fts_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_freetids td O2 O2_).
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
    assert (H1_1: obsr_equiv_freeqids td O1_ O1).
    {
      eapply obsr_equiv_fqs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_freeqids td O2 O2_).
    {
      eapply obsr_equiv_fqs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_fqs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_fqs_trans with (O2:=O1); eauto.
    
Qed. 

Lemma get_hwait_same:
  forall O1 O2 tls1 tls2 qls1 qls2 p1 st1 m1 sus1 p2 st2 m2 sus2 td' ms sz ts t1' t2' qid, 
    obsr_equiv_tskd td' O1 O2 -> 
    mq_wt_cond O1 ->
    mq_wt_cond O2 ->              
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) ->
    get tls1 t1' = Some (p1, st1, m1, sus1, td') -> 
    get tls2 t2' = Some (p2, st2, m2, sus2, td') -> 
    get O1 quelsid = Some (absecblist qls1) ->
    get O2 quelsid = Some (absecblist qls2) ->
    get qls1 qid = Some (msgq ms sz ts, td') ->
    get qls2 qid = Some (msgq ms sz ts, td') -> 
    GetHWait tls1 ts t1' -> 
    GetHWait tls2 ts t2' -> 
    t1' = t2'.
Proof.
  introv Hoe Hmwc1 Hmwc2 Hgtls1 Hgtls2 Hgt1' Hgt2' Hgqls1 Hgqls2.
  introv Hgq1 Hgq2 Hgh1 Hgh2.
  destruct Hgh1 as (Hin1 & Hh1).
  destruct Hgh2 as (Hin2 & Hh2).
  destruct Hh1 as (p1_ & st1_ & m1_ & su1 & d1 & Hgt1'_ & Hall1).
  destruct Hh2 as (p2_ & st2_ & m2_ & su2 & d2 & Hgt2'_ & Hall2).
  unfolds in Hmwc1.
  assert (Hall1_:
           forall t,
             In t ts ->
             exists pr msg0 sus to,
               get tls1 t = Some (pr, wait (os_stat_qpend qid) to, msg0, sus, td')).
  {
    introv Hin.
    lets H__: Hmwc1 qid Hgqls1 Hgtls1 Hgq1 Hin.
    auto.
  }
  assert (Hall2_:
           forall t,
             In t ts ->
             exists pr msg0 sus to,
               get tls2 t = Some (pr, wait (os_stat_qpend qid) to, msg0, sus, td')).
  {
    introv Hin.
    lets H__: Hmwc2 qid Hgqls2 Hgtls2 Hgq2 Hin.
    auto.
  }
  casetac t1' t2' He Hne; auto.

  Set Printing Implicit.
  unfold priority in Hgt1'.
  rewrite Hgt1' in Hgt1'; symmetry in Hgt1'; inverts Hgt1'.
  unfold priority in Hgt2'.
  rewrite Hgt2' in Hgt2'; symmetry in Hgt2'; inverts Hgt2'.
  Unset Printing Implicit.

  assert (d1 = td').
  {
    specialize (Hall1_ t1' Hin1).
    destruct Hall1_ as (pr1 & msg1_ & sus1_ & to1 & Hgt1'').
    unfolds in Hgt1''. unfolds in Hgt1'_.
    unfold TcbMap in Hgt1''.
    unfold TcbMap in Hgt1'_.
    rewrite Hgt1'' in Hgt1'_.
    inverts Hgt1'_.
    auto.
  }
  subst d1.
  assert (d2 = td').
  {
    specialize (Hall2_ t2' Hin2).
    destruct Hall2_ as (pr2 & msg2_ & sus2_ & to2 & Hgt2'').
    unfolds in Hgt2''. unfolds in Hgt2'_.
    unfold TcbMap in Hgt2''.
    unfold TcbMap in Hgt2'_.
    rewrite Hgt2'' in Hgt2'_.
    inverts Hgt2'_.
    auto.
  }
  subst d2.

  specialize (Hall1 t2' Hne Hin2).
  destruct Hall1 as (p' & st' & m' & su' & d' & Hgt2' & Hltu).
  
  specialize (Hall2 t1' (not_eq_sym Hne) Hin1).
  destruct Hall2 as (p'_ & st'_ & m'_ & su'_ & d'_ & Hgt1'' & Hltu').

  lets H_: dte_ex_tsk_in_dom_same t2' Hoe Hgtls1 Hgtls2.
  assert (Hex: exists pr0 st m sus0, get tls2 t2' = Some (pr0, st, m, sus0, td')).
  {
    do 4 eexists; eauto.
  }
  apply H_ in Hex.
  destruct Hex as (pr12 & st12 & m12 & sus12 & Hg12).
  Set Printing Implicit. 
  unfold priority in Hg12.
  Unset Printing Implicit.
  rewrite Hgt2' in Hg12; inverts Hg12.
  clear H_.
  
  lets H__: obsr_equiv_data_tsk_eq Hoe Hgtls1 Hgtls2 Hgt2' Hgt2'_.
  simpljoin.

  lets H_: dte_ex_tsk_in_dom_same t1' Hoe Hgtls1 Hgtls2.
  assert (Hex: exists pr0 st m sus0, get tls1 t1' = Some (pr0, st, m, sus0, td')).
  {
    do 4 eexists; eauto.
  }
  apply H_ in Hex.
  destruct Hex as (pr21 & st21 & m21 & sus21 & Hg21).
  Set Printing Implicit. 
  unfold priority in Hg21.
  Unset Printing Implicit.
  rewrite Hgt1'' in Hg21; inverts Hg21.
  clear H_.

  lets H__: obsr_equiv_data_tsk_eq Hoe Hgtls1 Hgtls2 Hgt1'_ Hgt1''.
  simpljoin.
  rename pr21 into pr1_. rename p2_ into pr2_.
  clear -Hltu Hltu'.

  false.
  apply Int.ltu_inv in Hltu.
  apply Int.ltu_inv in Hltu'.
  auto with zarith.
Qed.

Lemma qpost_confidentiality_oblig:
  forall t O1 O2 a vl ac1 ac2 vl1' vl2' O1' O2' td
         (Hpre2 : pre2 t O1 O2 (tsk_mq_same_dom (Vptr a :: vl)) td obsr_equiv_data flows_to)
         (Hpost1 : qpost_before_sched t (Vptr a :: vl) O1 ac1 (vl1', O1'))
         (Hpost2 : qpost_before_sched t (Vptr a :: vl) O2 ac2 (vl2', O2')), 
    (* (Hnex1 : ~ (exists cid, ac1 = _TickAct cid)) *)
    (* (Hnex2 : ~ (exists cid, ac2 = _TickAct cid)) *)
    obsr_equiv_tskd td O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'. 
Proof.
  intros.
  des_pre2 Hpre2.
  unfolds in Hpost1.
  unfolds in Hpost2.
  destruct Hpost1 as (msg1 & qid1 & Hptreq1 & Hmt1).
  destruct Hpost2 as (msg2 & qid2 & Hptreq2 & Hmt2).
  inverts Hptreq1.
  inverts Hptreq2.
  rename msg2 into msg.
  rename qid2 into qid.
  assert (Hor: (exists m, msg = Vptr m) \/ ~exists m, msg = Vptr m) by tauto.
  destruct Hor as [Hptr | Hnptr].
  -
    destruct Hptr as (m & Hmsg).
    subst msg.
    destruct Hmt1 as (qls1 & Hgqls1 & Hmt1).
    destruct Hmt2 as (qls2 & Hgqls2 & Hmt2).
    lets H_: dte_mq_cases qid Hdte' Hgqls1 Hgqls2.
    destruct (get qls1 qid) eqn: E1.
    +
      destruct p as (q & tdq).
      destruct q as [ms1 sz1 ts1].
      Set Printing Implicit.
      unfold tid in H_.
      rewrite E1 in H_.
      Unset Printing Implicit.
      lets H__: tq_same_dom_qdom Hpre11 Hsd1 Hgqls1 E1.
      subst tdq.
      destruct H_ as [Htdeq | Htdne].
      2: { destruct Htdne; tryfalse. }
      destruct Htdeq as (_ & Hgq2).
      rename E1 into Hgq1.
      rewrite Hgq2 in Hmt2.
      d_if_hyp.
      * rename ts1 into ts.
        rename ms1 into ms.
        rename sz1 into sz.
        destruct ts.
        ** simpljoin.
           splits; auto.             
           eapply qpost2_nowt_obsr_equiv_tskd; eauto.
        ** 
          destruct Hmt1 as (tls1 & t1' & p1 & st1 & m1 & sus1 & td1 & Hgtls1 & Hghwt1 & Hgt1' & HO1' & Hvl1' & Hac1).
          destruct Hmt2 as (tls2 & t2' & p2 & st2 & m2 & sus2 & td2 & Hgtls2 & Hghwt2 & Hgt2' & HO2' & Hvl2' & Hac2).
          subst.
          splits; auto.

          assert (Hghwt1_ := Hghwt1).
          assert (Hghwt2_ := Hghwt2).
          destruct Hghwt1 as (Hin_ts1 & Hh1).
          destruct Hghwt2 as (Hin_ts2 & Hh2).

          assert (td1 = td').
          {
            destruct Hpre11 as (Hp1 & Hinv1).
            lets H1_: Hinv1.(inv_mq_wt) Hgqls1 Hgtls1 Hgq1 Hin_ts1.
            rewrite Hgt1' in H1_.
            simpljoin.
            inverts H.
            auto.
          }
          subst td1.

          assert (td2 = td').
          {
            destruct Hpre12 as (Hp2 & Hinv2).
            lets H2_: Hinv2.(inv_mq_wt) Hgqls2 Hgtls2 Hgq2 Hin_ts2.
            rewrite Hgt2' in H2_.
            simpljoin.
            inverts H.
            auto.
          }
          subst td2.

          assert (t1' = t2').
          {
            simpl in Hdte'.
            lets H_: get_hwait_same Hdte'; eauto.
            eapply H_; eauto.
            apply Hpre11.
            apply Hpre12.
          }
          subst t1'.
          rename t2' into t'.

          eapply qpost2_obsr_equiv_tskd; eauto.
          
      * (* queues are full *)
        inv_errp.
        inv_errp.
        splits; eauto.
    +
      Set Printing Implicit.
      unfold tid in H_.
      rewrite E1 in H_.
      Unset Printing Implicit.
      destruct (get qls2 qid) eqn: E2.
      * destruct p as (q2 & tdq2).
        destruct q2 as [ms2 sz2 ts2].
        lets H__: tq_same_dom_qdom Hpre12 Hsd2 Hgqls2 E2.
        false. 
      *
        inv_errp.
        inv_errp.
        splits; eauto.

  -
    assert (Herr1: err_prop OS_ERR_INVALID_MSG vl1' O1 O1' ac1).
    {
      destruct msg; simpl in Hmt1; auto.
      false.
      apply Hnptr.
      eexists; eauto.
    }
    assert (Herr2: err_prop OS_ERR_INVALID_MSG vl2' O2 O2' ac2).
    {
      destruct msg; simpl in Hmt2; auto.
      false.
      apply Hnptr.
      eexists; eauto.
    }
    clear Hmt1 Hmt2.
    inv_errp. inv_errp.
    splits; eauto.    
Qed. 




Lemma qpost_nowt_prsv_inv:
  forall O qls qid ms sz tdq m,
    I O ->
    get O quelsid = Some (absecblist qls) ->
    get qls qid = Some (msgq ms sz nil, tdq) ->
    I (set O quelsid
         (absecblist
            (set qls qid (msgq (ms ++ m :: nil) sz nil, tdq)))).
Proof.
  introv Hinv Hgqls Hgq.
  set (O' := set O quelsid
               (absecblist
                  (set qls qid (msgq (ms ++ m :: nil) sz nil, tdq)))).
  assert (Hneq_tq : abstcblsid <> quelsid).
  { introv Hf; inverts Hf. }
  assert (Hneq_fq : freeqid <> quelsid).
  { introv Hf; inverts Hf. }
  assert (Hneq_chq : chlsid <> quelsid).
  { introv Hf; inverts Hf. }
  assert (Htls : get O abstcblsid = get O' abstcblsid).
  { unfold O'. rewrite neq_set_get; eauto. }
  assert (Hfqs : get O freeqid = get O' freeqid).
  { unfold O'. rewrite neq_set_get; eauto. }
  assert (Hchs : get O chlsid = get O' chlsid).
  { unfold O'. rewrite neq_set_get; eauto. }
  assert (Hactive : forall q td,
             ex_active_que O' q td <-> ex_active_que O q td).
  {
    introv.
    unfold ex_active_que, O'.
    split; intros Hex; simpljoin.
    - rewrite map_get_set in H.
      inverts H.
      casetac qid q He Hne.
      + subst. rewrite map_get_set in H0. inverts H0.
        do 4 eexists; split; [exact Hgqls | exact Hgq].
      + rewrite neq_set_get in H0; eauto.
        do 4 eexists; split; [exact Hgqls | exact H0].
    - rewrite Hgqls in H. inverts H.
      rewrite map_get_set.
      casetac qid q He Hne.
      + subst.
        Set Printing Implicit.
        unfold Modules.qid, tid in H0, Hgq.
        rewrite Hgq in H0. inverts H0.
        Unset Printing Implicit.
        do 4 eexists. split. { reflexivity. }
        Set Printing Implicit.
        unfold qid. rewrite map_get_set.
        Unset Printing Implicit.
        reflexivity.
      + do 4 eexists. split. { reflexivity. }
        Set Printing Implicit.
        unfold Modules.qid, tid in H0 |- *.
        rewrite neq_set_get; eauto.
        Unset Printing Implicit.
  }
  inverts Hinv.
  constructors.
  - eapply same_tsks_tsk_active_free_disj; eauto.
    unfold O'. rewrite neq_set_get; eauto.
    introv Hf; inverts Hf.
  - eapply same_tsks_tsk_dom_disj; eauto.
    unfold O'. rewrite neq_set_get; eauto.
    introv Hf; inverts Hf.
  - eapply same_tsks_tsk_diff_id_pr; eauto.
  - unfold que_active_free_disj in *.
    introv Hea Hef.
    eapply inv_que_af_disj with (q := q) (td := td).
    + apply Hactive; exact Hea.
    + eapply same_mqs_ex_free_que; [symmetry; exact Hfqs | exact Hef].
  - unfold que_dom_disj in *.
    introv Hsd1 Hsd2.
    apply inv_que_d_disj with (q := q).
    + destruct Hsd1 as [Ha | Hf].
      * left. apply Hactive; auto.
      * right. eapply same_mqs_ex_free_que; [symmetry; exact Hfqs | exact Hf].
    + destruct Hsd2 as [Ha | Hf].
      * left. apply Hactive; auto.
      * right. eapply same_mqs_ex_free_que; [symmetry; exact Hfqs | exact Hf].
  - unfold mq_wt_cond in *.
    introv Hgqls' Hgtls' Hgq' Hin.
    unfold O' in Hgqls'. rewrite map_get_set in Hgqls'. inverts Hgqls'.
    rewrite <- Htls in Hgtls'.
    casetac qid q He Hne.
    + subst. rewrite map_get_set in Hgq'. inverts Hgq'. simpl in Hin; false.
    + rewrite neq_set_get in Hgq'; eauto.
  - unfold wt_mq_cond in *.
    introv Hgtls' Hgt Hgqls'.
    rewrite <- Htls in Hgtls'.
    unfold O' in Hgqls'. rewrite map_get_set in Hgqls'. inverts Hgqls'.
    lets Hwt : inv_wt_mq Hgtls' Hgt Hgqls.
    destruct Hwt as (ms0 & sz0 & ts0 & Hgq0 & Hin).
    casetac qid q He Hne.
    + subst.
      Set Printing Implicit.
      unfold Modules.qid, tid in Hgq0, Hgq.
      rewrite Hgq in Hgq0. inverts Hgq0.
      Unset Printing Implicit.
      simpl in Hin; false.
    + do 3 eexists; split; eauto.
      rewrite neq_set_get; eauto.
  - eapply same_chs_chs_sat_config; eauto.
Qed.

Lemma qpost_nowt_guar_tsk:
  forall t O qid qls ms sz tdq m,
    get O quelsid = Some (absecblist qls) ->
    get qls qid = Some (msgq ms sz nil, tdq) ->
    guar_tsk_env t O
      (set O quelsid
         (absecblist
            (set qls qid (msgq (ms ++ Vptr m :: nil) sz nil, tdq)))).
Proof.
  introv Hgqls Hgq.
  unfolds.
  split.
  - introv Hneq Hsd.
    eapply same_tsks_sdom with (O := O); eauto.
    + rewrite neq_set_get; eauto. introv Hf; inverts Hf.
    + rewrite neq_set_get; eauto. introv Hf; inverts Hf.
  - introv Hqsd.
    destruct Hqsd as [Heaq | Hefq].
    + left.
      unfold ex_active_que in *.
      destruct Heaq as (qls0 & ms0 & sz0 & ts0 & Hgqls0 & Hgq0).
      rewrite Hgqls in Hgqls0. inverts Hgqls0.
      rewrite map_get_set.
      casetac qid q He Hne.
      * subst.
        Set Printing Implicit.
        unfold Modules.qid, tid in Hgq0, Hgq.
        rewrite Hgq in Hgq0. inverts Hgq0.
        Unset Printing Implicit.
        do 4 eexists. split. { reflexivity. }
        Set Printing Implicit.
        unfold qid. rewrite map_get_set.
        Unset Printing Implicit.
        reflexivity.
      * do 4 eexists. split. { reflexivity. }
        Set Printing Implicit.
        unfold Modules.qid, tid in Hgq0 |- *.
        rewrite neq_set_get; eauto.
        Unset Printing Implicit.
    + right.
      unfold ex_free_que in *.
      rewrite neq_set_get; eauto.
      introv Hf; inverts Hf.
Qed.

Lemma sdom_set_quel_iff:
  forall O qls t td,
    sdom O t td <->
    sdom (set O quelsid (absecblist qls)) t td.
Proof.
  intros.
  unfold sdom, state, sdom_, ex_active_tsk, ex_free_tsk.
  rewrite neq_set_get.
  2: { introv Hf; inverts Hf. }
  rewrite neq_set_get.
  2: { introv Hf; inverts Hf. }
  tauto.
Qed.


Require Import ver_mq_pend.


Lemma qpost_wt_prsv_inv:
  forall t O qid m qls ms sz t0 l tdq tls t' p st m0 sus td,
    pre1 t O (tsk_mq_same_dom (Vptr qid :: Vptr m :: nil)) ->
    get O quelsid = Some (absecblist qls) ->
    get qls qid = Some (msgq ms sz (t0 :: l), tdq) ->
    get O abstcblsid = Some (abstcblist tls) ->
    GetHWait tls (t0 :: l) t' ->
    get tls t' = Some (p, st, m0, sus, td) ->
    I
      (set
         (set O abstcblsid
            (abstcblist (set tls t' (p, rdy, Vptr m, sus, td))))
         quelsid
         (absecblist
            (set qls qid
               (msgq ms sz (remove_tid t' (t0 :: l)), tdq)))).
Proof.
  introv Hpre Hgqls Hgq Hgtls Hghwt Hgt'.
  destruct Hpre as (Hsame & Hinv).
  destruct Hghwt as (Hin' & Hhighest).
  lets Htw: Hinv.(inv_mq_wt) Hgqls Hgtls Hgq Hin'.
  destruct Htw as (prw & msgw & susw & tow & Hgtw).
  rewrite Hgt' in Hgtw. inverts Hgtw.
  inverts Hinv.
  constructors.
  - unfold tsk_active_free_disj in *.
    introv Hactive Hfree.
    eapply inv_tsk_af_disj.
    + eapply qpend_ex_active_task_rev; eauto.
    + eapply qpend_ex_free_task_rev; eauto.
  - eapply qpend_tsk_dom_disj_update; eauto.
  - eapply qpend_tsk_diff_id_prio_update; eauto.
  - unfold que_active_free_disj in *.
    introv Hactive Hfree.
    eapply inv_que_af_disj.
    + eapply qpend_ex_active_que_rev; eauto.
    + eapply qpend_ex_free_que_rev; eauto.
  - eapply qpend_que_dom_disj_update; eauto.
  - unfold mq_wt_cond in *.
    introv Hgqls' Hgtls' Hgq' Hin.
    rewrite map_get_set in Hgqls'.
    rewrite neq_set_get in Hgtls'; eauto.
    2: { introv Hf; inverts Hf. }
    rewrite map_get_set in Hgtls'.
    inverts Hgqls'; inverts Hgtls'.
    casetac qid q Heq Hneq.
    + subst. rewrite map_get_set in Hgq'. inverts Hgq'.
      assert (Hin0 : List.In t1 (t0 :: l)).
      { eapply in_remove_tid; eauto. }
      lets Hw: inv_mq_wt Hgqls Hgtls Hgq Hin0.
      destruct Hw as (pr & msg & sus0 & to & Hgetw).
      casetac t' t1 Het Hnet.
      * subst.
        change (List.In t1 (remove_tid t1 (t0 :: l))) in Hin.
        apply in_remove_tid_false in Hin. false.
      * do 4 eexists. rewrite neq_set_get; eauto.
    + rewrite neq_set_get in Hgq'; eauto.
      lets Hw: inv_mq_wt Hgqls Hgtls Hgq' Hin.
      destruct Hw as (pr & msg & sus0 & to & Hgetw).
      casetac t' t1 Het Hnet.
      * subst. rewrite Hgt' in Hgetw. inverts Hgetw. false.
      * do 4 eexists. rewrite neq_set_get; eauto.
  - unfold wt_mq_cond in *.
    introv Hgtls' Hgett Hgqls'.
    rewrite neq_set_get in Hgtls'; eauto.
    2: { introv Hf; inverts Hf. }
    rewrite map_get_set in Hgtls'.
    rewrite map_get_set in Hgqls'.
    inverts Hgtls'; inverts Hgqls'.
    casetac t' t1 Het Hnet.
    + subst. rewrite map_get_set in Hgett. inverts Hgett.
    + rewrite neq_set_get in Hgett; eauto.
      lets Hw: inv_wt_mq Hgtls Hgett Hgqls.
      destruct Hw as (ms0 & sz0 & ts0 & Hgetq & Hin).
      casetac qid q Heq Hneq.
      * subst.
        Set Printing Implicit.
        unfold Modules.qid, tid in Hgetq, Hgq.
        rewrite Hgq in Hgetq. inverts Hgetq.
        Unset Printing Implicit.
        do 3 eexists. split.
        ** rewrite map_get_set. reflexivity.
        ** change (List.In t1 (remove_tid t' (t0 :: l))).
           eapply in_remove_tid'; eauto.
      * do 3 eexists. split; eauto.
        rewrite neq_set_get; eauto.
  - unfold chs_sat_config in *.
    introv Hgchs Hgc.
    assert (Hcq : chlsid <> quelsid) by (introv Hf; inverts Hf).
    assert (Hct : chlsid <> abstcblsid) by (introv Hf; inverts Hf).
    rewrite neq_set_get in Hgchs; auto.
    rewrite neq_set_get in Hgchs; auto.
    eapply inv_chcfg; eauto.
Qed.


Lemma qpost_wt_guar_tsk:
  forall t O qid m qls ms sz ts tdq tls t' p st m0 sus td,
    get O quelsid = Some (absecblist qls) ->
    get qls qid = Some (msgq ms sz ts, tdq) ->
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t' = Some (p, st, m0, sus, td) ->
    guar_tsk_env t O
      (set
         (set O abstcblsid
            (abstcblist (set tls t' (p, rdy, Vptr m, sus, td))))
         quelsid
         (absecblist
            (set qls qid (msgq ms sz (remove_tid t' ts), tdq)))).
Proof.
  introv Hgqls Hgq Hgtls Hgt'.
  unfold guar_tsk_env.
  split.
  - introv Hneq Hsd.
    unfold sdom, state in *.
    rewrite <- qpend_sdom_update_iff; eauto.
  - introv Hqsd.
    rewrite <- qpend_q_sdom_update_iff; eauto.
Qed.

Lemma qpost_wt_sdom_iff:
  forall O qls qid ms sz ts tdq tls t' p st m0 sus td m t0 td0,
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t' = Some (p, st, m0, sus, td) ->
    sdom O t0 td0 <->
    sdom
      (set
         (set O abstcblsid
            (abstcblist (set tls t' (p, rdy, Vptr m, sus, td))))
         quelsid
         (absecblist
            (set qls qid (msgq ms sz (remove_tid t' ts), tdq))))
      t0 td0.
Proof.
  introv Hgtls Hgt'.
  unfold sdom, state.
  eapply qpend_sdom_update_iff; eauto.
Qed.






Lemma dr_qpost_before_schd:
  forall t a vl,
    deduct_rules t (rly_tsk_env t) (guar_tsk_env t) flows_to obsr_equiv_data
      (tsk_mq_same_dom (Vptr a :: vl) # qpost_before_sched [|Vptr a :: vl|]) 
      (qpost_before_schd_post (Vptr a :: vl)).
Proof.
  intros.
  constructors.
  - apply stable_pre_tq_same_d.
  - introv Hpre1 Hqbs.
    unfolds in Hqbs.
    destruct Hqbs as (msg & qid & Hptreq & Hmt).
    inverts Hptreq.
    assert (Hor: (exists m, msg = Vptr m) \/ ~exists m, msg = Vptr m) by tauto.
    destruct Hor.
    +
      destruct H as (m & Hmsg).
      subst msg.
      destruct Hmt as (qls & Hgqls & Hmt).
      d_mt_hyp.
      *
        destruct p as (q & tdq).
        destruct q as [ms sz ts].
        d_if_hyp.
        **
          d_mt_hyp.
          { (* no task waiting to receive *)
            simpljoin; subst. 
            splits.
            - 
              unfolds.
              splits.
              + unfolds. eexists; eauto.
              + eapply qpost_nowt_prsv_inv; eauto.
                apply Hpre1.
              + eapply qpost_nowt_guar_tsk; eauto.
            -
              intros.
              apply sdom_set_quel_iff.  
            -
              introv Hf. inverts Hf.
            -
              introv Hnex Hsd Hnfl.
              eapply qpost_integrity_oblig1; eauto.
          }
          { (* some tasks waiting to receive *)
            destruct Hmt as (tls & t' & p & st & m0 & sus & td & Hgtls & Hghwt & Hgt' & HO' & Hvl' & Hac).
            subst. 
            splits.
            - 
              unfolds.
              splits.
              + unfolds. eexists; eauto.
              + eapply qpost_wt_prsv_inv; eauto.
              + eapply qpost_wt_guar_tsk; eauto.
            -
              intros. 
              eapply qpost_wt_sdom_iff; eauto.
            -
              introv Hf. inverts Hf.
            -
              introv Hnex Hsd Hnfl.
              eapply qpost_integrity_oblig2; eauto.
          }
        **
          {
            inv_errp.
            splits.
            *
              unfolds.
              splits.
              ** unfolds. eexists; eauto.
              ** eapply Hpre1; eauto.
              ** apply guar_tsk_refl.
            *
              intros. tauto.
            *
              introv Hf. inverts Hf.
            *
              introv Hnex Hsd Hnfl.
              apply obsr_equiv_data_refl.            
          }          
      *
        {
          inv_errp.
          splits.
          *
            unfolds.
            splits.
            ** unfolds. eexists; eauto.
            ** eapply Hpre1; eauto.
            ** apply guar_tsk_refl.
          *
            intros. tauto.
          *
            introv Hf. inverts Hf.
          *
            introv Hnex Hsd Hnfl.
            apply obsr_equiv_data_refl.
        }        
    +
      assert (Herr: err_prop OS_ERR_INVALID_MSG vl' O O' ac).
      {
        d_mt_hyp; auto.
        false. apply H. eexists; eauto.
      }
      inv_errp.
      splits.
      *
        unfolds.
        splits.
        ** unfolds. eexists; eauto.
        ** eapply Hpre1; eauto.
        ** apply guar_tsk_refl.
      *
        intros. tauto.
      *
        introv Hf. inverts Hf.
      *
        introv Hnex Hsd Hnfl.
        apply obsr_equiv_data_refl.
  -
    (* confidentiality oblig. *)
    introv Hpre2 Hpost1 Hpost2 Hnex1 Hnex2.
    simpl.
    eapply qpost_confidentiality_oblig; eauto.
Qed.

Lemma dr_qpost: 
  forall vl t, 
    tl_vl_match (Tptr Tvoid :: Tptr Tvoid :: nil) vl = true -> 
    deduct_rules t (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (mq_apispecs.qpost vl) q_star. 
Proof.
  introv Htvm.
  constructors.
  
  - (* qpend_check_dom ... *)
    instantiate (1 := chk_dom_post vl).
    constructors.
    + 
      apply stable_pre_trivial_asrt.
    +
      introv Hpre1 Hchk_d.
      unfolds in Hchk_d.
      d_mt_hyp; simpl in Htvm; tryfalse.
      d_mt_hyp; simpl in Htvm; tryfalse.  
      *
        inverts Hchk_d.
        simpljoin.
        splits.
        ** unfolds.
           splits.
           ***
             unfolds.
             split.
             { eexists; eauto. } 
             { introv Heq. inverts Heq. }
           ***
             unfolds in Hpre1.
             simpljoin; auto.
           ***
             apply guar_tsk_refl.
        ** tauto.
        ** introv Hf; inverts Hf.
        ** introv Hf. clear Hf.
           intros.
           apply obsr_equiv_data_refl.
      *
        destruct Hchk_d as (tls & pr & st & msg & sus & td & qls & Hgtls & Hgt & Hgqls & Hmtq).
        d_mt_hyp.
        **
          destruct p as (q & td_).
          destruct q as [ms sz ts].
          destruct Hmtq as (Horq & HeqO & Hac).
          subst O' ac.  
          splits.
          ***
            unfolds. splits.
            ****
              eapply chk_dom_post_holds; eauto.
              {
                destruct Horq; simpljoin; eexists; eauto.
              }
            ****
              unfolds in Hpre1; simpljoin; auto.
            ****
              apply guar_tsk_refl.
          ***
            tauto.
          ***
            introv Hf; inverts Hf.
          ***
            intros.
            apply obsr_equiv_data_refl.
        **
          simpljoin.
          splits.
          ***
            unfolds.
            unfolds in Hpre1.
            simpljoin; splits; eauto.
            ****
              unfold chk_dom_post.
              split.
              { eexists; eauto. }
              introv Hf. inverts Hf.
            ****
              apply guar_tsk_refl.
          ***
            tauto.
          ***
            introv Hf; inverts Hf.
          ***
            intros.
            apply obsr_equiv_data_refl.
    +
      introv Hpre2 Hchkd1 Hchkd2 Hntck1 Hntck2.
      unfolds in Hpre2.
      des_pre2 Hpre2. 
      lets H_: dte_check_dom_prsv Htvm Hpre11 Hpre12 Hdte; eauto.
  -
    introv Hinv Hq.
    introv Hs2.
    d_mt_hyp.
    +
      subst.
      split.
      * apply ssp_end.
      * constructors.
    +
      d_mt_hyp; 
        subst; 
        try (split; [ apply ssp_end | constructors; eapply stable_post_true; eauto ]; fail).

      unfolds in Hq.
      destruct Hq as (Hex & Heqd).
      destruct Hex as (i0 & Heqi).
      inverts Heqi.
      destruct (Int.eq_dec i0 dom_chk_ok).
      * subst i0.
        change (Int.eq dom_chk_ok dom_chk_ok) with true.
        simpl.
        specialize (Heqd (eq_refl _)).
        destruct vl; simpl in Htvm; tryfalse.
        destruct v; simpl in Htvm; tryfalse.
        ** (* Vnull *)
          clear Heqd.
          split.
          ***
            unfolds; auto.
          ***
            eapply seq_rule with (q' := q_bot); eauto.
            constructors.
            {
              unfold tsk_mq_same_dom.
              apply stable_pre_trivial_asrt.
            }
            {
              introv Hpre1 Hpost.
              unfolds in Hpost.
              simpljoin; tryfalse.
            }
            {
              introv Hpre2 Hpost1 Hpost2 Hntck1 Hntck2.
              unfolds in Hpost1.
              simpljoin; tryfalse.
            }
            {
              introv Hinv_ Hbot.
              unfolds in Hbot.
              false.
            }
              
        ** (* Vptr _ *)
          specializes Heqd; eauto.
          split.
          {
            unfolds.
            auto.
          }
          {
            clear Heqd.
            eapply seq_rule with (q':=qpost_before_schd_post (Vptr a :: vl)).
            {
              eapply dr_qpost_before_schd; eauto.
            }
            {
              introv Hinv_ Hpost Hs2.
              subst.
              unfolds in Hpost.
              destruct Hpost as (z & Hvl').
              subst vl0.
              split.
              - unfolds. simpl. unfolds; auto.
              - constructors.
                + eapply dr_sched; eauto.
                + introv Hi Hq_ Hs2.
                  subst s2.
                  split.
                  * apply ssp_end.
                  * constructors. 
            }
          }
          
      * asserts_rewrite (Int.eq i0 dom_chk_ok = false).
        {
          apply Int.eq_false. auto.
        }
        destruct (Int.eq_dec i0 dom_chk_err).
        **
          subst i0.
          change (Int.eq dom_chk_err dom_chk_err) with true.
          simpl.
          split.
          ***
            unfolds; auto.
          ***
            constructors. 
        **
          asserts_rewrite (Int.eq i0 dom_chk_err = false). 
          {
            apply Int.eq_false. auto.
          }          
          split.
          ***
            apply ssp_end. 
          ***
            constructors. 
Qed. 
        
      
