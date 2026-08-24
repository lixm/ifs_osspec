
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

    
Lemma pend_tsk_active_free_disj_prsv:
  forall O q vl_ ac vl' O' t,
    tsk_active_free_disj O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    tsk_active_free_disj O'.
Proof.
  introv Htafd Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        unfold tsk_active_free_disj in *.
        intros t' td' Hactive Hfree.
        unfold ex_active_tsk in Hactive.
        destruct Hactive as
            (tls0 & pr0 & st0 & msg0 & sus0 & Hgettls0 & Hgett0).
        rewrite neq_set_get in Hgettls0; eauto.
        2: { introv Hf; inverts Hf. }
        rewrite map_get_set in Hgettls0.
        inverts Hgettls0.
        assert (Hactive0 : ex_active_tsk O t' td').
        {
          unfold ex_active_tsk.
          casetac t t' He Hne.
          - subst.
            rewrite map_get_set in Hgett0.
            inverts Hgett0.
            do 5 eexists; splits; eauto.
          - rewrite neq_set_get in Hgett0; eauto.
            do 5 eexists; splits; eauto.
        }
        assert (Hfree0 : ex_free_tsk O t' td').
        {
          unfold ex_free_tsk in *.
          destruct Hfree as (fts & ts0 & Hgetfts & Hgetts & Hin).
          rewrite neq_set_get in Hgetfts.
          2: { introv Hf; inverts Hf. }
          rewrite neq_set_get in Hgetfts.
          2: { introv Hf; inverts Hf. }
          do 2 eexists; splits; eauto.
        }
        exact (Htafd t' td' Hactive0 Hfree0).
      * simpljoin.
        tryfalse.
        subst.
        unfold tsk_active_free_disj in *.
        intros t' td' Hactive Hfree.
        unfold ex_active_tsk in Hactive.
        destruct Hactive as
            (tls0 & pr0 & st0 & msg0 & sus0 & Hgettls0 & Hgett0).
        rewrite neq_set_get in Hgettls0; eauto.
        2: { introv Hf; inverts Hf. }
        rewrite map_get_set in Hgettls0.
        inverts Hgettls0.
        assert (Hactive0 : ex_active_tsk O t' td').
        {
          unfold ex_active_tsk.
          casetac t t' He Hne.
          - subst.
            rewrite map_get_set in Hgett0.
            inverts Hgett0.
            do 5 eexists; splits; eauto.
          - rewrite neq_set_get in Hgett0; eauto.
            do 5 eexists; splits; eauto.
        }
        assert (Hfree0 : ex_free_tsk O t' td').
        {
          unfold ex_free_tsk in *.
          destruct Hfree as (fts & ts0 & Hgetfts & Hgetts & Hin).
          rewrite neq_set_get in Hgetfts.
          2: { introv Hf; inverts Hf. }
          rewrite neq_set_get in Hgetfts.
          2: { introv Hf; inverts Hf. }
          do 2 eexists; splits; eauto.
        }
        exact (Htafd t' td' Hactive0 Hfree0).
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.

Lemma qpend_ex_active_task_rev:
  forall O tls qls' p st msg sus td st' msg' t t0 td',
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, msg, sus, td) ->
    ex_active_tsk
      (set (set O abstcblsid
                (abstcblist (set tls t (p, st', msg', sus, td))))
           quelsid (absecblist qls')) t0 td' ->
    ex_active_tsk O t0 td'.
Proof.
  introv Hgettls Hgett Hactive.
  unfold ex_active_tsk in *.
  destruct Hactive as
      (tls0 & pr0 & st0 & msg0 & sus0 & Hgettls0 & Hgett0).
  rewrite neq_set_get in Hgettls0.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set in Hgettls0.
  inverts Hgettls0.
  casetac t t0 He Hne.
  - subst.
    rewrite map_get_set in Hgett0.
    inverts Hgett0.
    do 5 eexists.
    split.
    + exact Hgettls.
    + exact Hgett.
  - rewrite neq_set_get in Hgett0; eauto.
    do 5 eexists.
    split.
    + exact Hgettls.
    + exact Hgett0.
Qed.

Lemma qpend_ex_free_task_rev:
  forall O tls' qls' t0 td',
    ex_free_tsk
      (set (set O abstcblsid (abstcblist tls'))
           quelsid (absecblist qls')) t0 td' ->
    ex_free_tsk O t0 td'.
Proof.
  introv Hfree.
  unfold ex_free_tsk in *.
  destruct Hfree as (fts & ts & Hgetfts & Hgetts & Hin).
  rewrite neq_set_get in Hgetfts.
  2: { introv Hf; inverts Hf. }
  rewrite neq_set_get in Hgetfts.
  2: { introv Hf; inverts Hf. }
  do 2 eexists; splits; eauto.
Qed.

Lemma qpend_tsk_dom_disj_update:
  forall O tls qls' p st msg sus td st' msg' t,
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, msg, sus, td) ->
    tsk_dom_disj O ->
    tsk_dom_disj
      (set (set O abstcblsid
                (abstcblist (set tls t (p, st', msg', sus, td))))
           quelsid (absecblist qls')).
Proof.
  introv Hgettls Hgett Hdisj.
  unfold tsk_dom_disj in *.
  intros t0 td1 td2 Hsd1 Hsd2.
  assert (Hsd01 : sdom_ O t0 td1).
  {
    unfold sdom_ in *.
    destruct Hsd1 as [Hactive | Hfree].
    - left. eapply qpend_ex_active_task_rev; eauto.
    - right. eapply qpend_ex_free_task_rev; eauto.
  }
  assert (Hsd02 : sdom_ O t0 td2).
  {
    unfold sdom_ in *.
    destruct Hsd2 as [Hactive | Hfree].
    - left. eapply qpend_ex_active_task_rev; eauto.
    - right. eapply qpend_ex_free_task_rev; eauto.
  }
  exact (Hdisj t0 td1 td2 Hsd01 Hsd02).
Qed.

Lemma pend_tsk_dom_disj_prsv:
  forall O q vl_ ac vl' O' t,
    tsk_dom_disj O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    tsk_dom_disj O'.
Proof.
  introv Hdisj Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_tsk_dom_disj_update; eauto.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_tsk_dom_disj_update; eauto.
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.


Lemma qpend_tsk_diff_id_prio_update:
  forall O tls qls' t p st msg sus td st' msg',
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, msg, sus, td) ->
    tsk_diff_id_prio O ->
    tsk_diff_id_prio
      (set
         (set O abstcblsid
            (abstcblist (set tls t (p, st', msg', sus, td))))
         quelsid (absecblist qls')).
Proof.
  introv Hgettls Hgett Hdiff.
  unfold tsk_diff_id_prio in *.
  rewrite neq_set_get.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set.
  intros tls0 Heqtls t1 t2 td0 pr1 st1 msg1 sus1
         pr2 st2 msg2 sus2 Hneq Hget1 Hget2.
  inverts Heqtls.
  casetac t t1 He1 Hne1.
  - subst.
    rewrite map_get_set in Hget1.
    inverts Hget1.
    rewrite neq_set_get in Hget2; eauto.
  - rewrite neq_set_get in Hget1; eauto.
    casetac t t2 He2 Hne2.
    + subst.
      rewrite map_get_set in Hget2.
      inverts Hget2.
      eauto.
    + rewrite neq_set_get in Hget2; eauto.
Qed.

Lemma pend_tsk_diff_id_prio_prsv:
  forall O q vl_ ac vl' O' t,
    tsk_diff_id_prio O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    tsk_diff_id_prio O'.
Proof.
  introv Hdiff Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_tsk_diff_id_prio_update; eauto.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_tsk_diff_id_prio_update; eauto.
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.

Lemma que_active_free_disj_prsv:
  forall O q vl_ ac vl' O' t,
    que_active_free_disj O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    que_active_free_disj O'.
Proof.
  introv Hdisj Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  match goal with
  | Hvl : Vptr q :: vl_ = Vptr _ :: _ |- _ => inverts Hvl
  end.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        unfold que_active_free_disj in *.
        intros q0 td0 Hactive Hfree.
        assert (Hactive0 : ex_active_que O q0 td0).
        {
          unfold ex_active_que in *.
          destruct Hactive as
              (qls0 & ms0 & sz0 & ts0 & Hgetqls0 & Hgetq0).
          rewrite map_get_set in Hgetqls0.
          inverts Hgetqls0.
          casetac x q0 He Hne.
          - subst.
            rewrite map_get_set in Hgetq0.
            inverts Hgetq0.
            do 4 eexists; splits; eauto.
          - rewrite neq_set_get in Hgetq0; eauto.
            do 4 eexists; splits; eauto.
        }
        assert (Hfree0 : ex_free_que O q0 td0).
        {
          unfold ex_free_que in *.
          destruct Hfree as (fqs & qs & Hgetfqs & Hgetqs & Hin).
          rewrite neq_set_get in Hgetfqs.
          2: { introv Hf; inverts Hf. }
          rewrite neq_set_get in Hgetfqs.
          2: { introv Hf; inverts Hf. }
          do 2 eexists; splits; eauto.
        }
        exact (Hdisj q0 td0 Hactive0 Hfree0).
      * simpljoin.
        tryfalse.
        subst.
        unfold que_active_free_disj in *.
        intros q0 td0 Hactive Hfree.
        assert (Hactive0 : ex_active_que O q0 td0).
        {
          unfold ex_active_que in *.
          destruct Hactive as
              (qls0 & ms0 & sz0 & ts0 & Hgetqls0 & Hgetq0).
          rewrite map_get_set in Hgetqls0.
          inverts Hgetqls0.
          casetac x q0 He Hne.
          - subst.
            rewrite map_get_set in Hgetq0.
            inverts Hgetq0.
            do 4 eexists; splits; eauto.
          - rewrite neq_set_get in Hgetq0; eauto.
            do 4 eexists; splits; eauto.
        }
        assert (Hfree0 : ex_free_que O q0 td0).
        {
          unfold ex_free_que in *.
          destruct Hfree as (fqs & qs & Hgetfqs & Hgetqs & Hin).
          rewrite neq_set_get in Hgetfqs.
          2: { introv Hf; inverts Hf. }
          rewrite neq_set_get in Hgetfqs.
          2: { introv Hf; inverts Hf. }
          do 2 eexists; splits; eauto.
        }
        exact (Hdisj q0 td0 Hactive0 Hfree0).
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.


Lemma qpend_ex_active_que_rev:
  forall O qls tls' q ms sz ts td ms' ts' q0 td0,
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq ms sz ts, td) ->
    ex_active_que
      (set (set O abstcblsid (abstcblist tls'))
           quelsid (absecblist (set qls q (msgq ms' sz ts', td))))
      q0 td0 ->
    ex_active_que O q0 td0.
Proof.
  introv Hgetqls Hgetq Hactive.
  unfold ex_active_que in *.
  destruct Hactive as
      (qls0 & ms0 & sz0 & ts0 & Hgetqls0 & Hgetq0).
  rewrite map_get_set in Hgetqls0.
  inverts Hgetqls0.
  casetac q q0 He Hne.
  - subst.
    rewrite map_get_set in Hgetq0.
    inverts Hgetq0.
    do 4 eexists; splits; eauto.
  - rewrite neq_set_get in Hgetq0; eauto.
    do 4 eexists; splits; eauto.
Qed.

Lemma qpend_ex_free_que_rev:
  forall O qls' tls' q0 td0,
    ex_free_que
      (set (set O abstcblsid (abstcblist tls'))
           quelsid (absecblist qls')) q0 td0 ->
    ex_free_que O q0 td0.
Proof.
  introv Hfree.
  unfold ex_free_que in *.
  destruct Hfree as (fqs & qs & Hgetfqs & Hgetqs & Hin).
  rewrite neq_set_get in Hgetfqs.
  2: { introv Hf; inverts Hf. }
  rewrite neq_set_get in Hgetfqs.
  2: { introv Hf; inverts Hf. }
  do 2 eexists; splits; eauto.
Qed.

Lemma qpend_que_dom_disj_update:
  forall O qls tls' q ms sz ts td ms' ts',
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq ms sz ts, td) ->
    que_dom_disj O ->
    que_dom_disj
      (set (set O abstcblsid (abstcblist tls'))
           quelsid (absecblist (set qls q (msgq ms' sz ts', td)))).
Proof.
  introv Hgetqls Hgetq Hdisj.
  unfold que_dom_disj in *.
  intros q0 td1 td2 Hsd1 Hsd2.
  assert (Hsd01 : q_sdom_ O q0 td1).
  {
    unfold q_sdom_ in *.
    destruct Hsd1 as [Hactive | Hfree].
    - left. eapply qpend_ex_active_que_rev; eauto.
    - right. eapply qpend_ex_free_que_rev; eauto.
  }
  assert (Hsd02 : q_sdom_ O q0 td2).
  {
    unfold q_sdom_ in *.
    destruct Hsd2 as [Hactive | Hfree].
    - left. eapply qpend_ex_active_que_rev; eauto.
    - right. eapply qpend_ex_free_que_rev; eauto.
  }
  exact (Hdisj q0 td1 td2 Hsd01 Hsd02).
Qed.

Lemma que_dom_disj_prsv:
  forall O q vl_ ac vl' O' t,
    que_dom_disj O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    que_dom_disj O'.
Proof.
  introv Hdisj Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  match goal with
  | Hvl : Vptr q :: vl_ = Vptr _ :: _ |- _ => inverts Hvl
  end.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_que_dom_disj_update; eauto.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_que_dom_disj_update; eauto.
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.


Lemma qpend_mq_wt_immediate_update:
  forall O tls qls t p oldmsg sus td q m m0 ms sz ts qd,
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, rdy, oldmsg, sus, td) ->
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq (m0 :: ms) sz ts, qd) ->
    mq_wt_cond O ->
    mq_wt_cond
      (set
         (set O abstcblsid
            (abstcblist (set tls t (p, rdy, m, sus, td))))
         quelsid (absecblist (set qls q (msgq ms sz ts, qd)))).
Proof.
  introv Hgettls Hgett Hgetqls Hgetq Hmq.
  unfold mq_wt_cond in *.
  intros qls0 q0 ms0 sz0 ts0 td0 tls0 t0
         Hgetqls0 Hgettls0 Hgetq0 Hin.
  rewrite map_get_set in Hgetqls0.
  rewrite neq_set_get in Hgettls0.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set in Hgettls0.
  inverts Hgetqls0.
  inverts Hgettls0.
  casetac q q0 He Hne.
  - subst.
    rewrite map_get_set in Hgetq0.
    inverts Hgetq0.
    lets Hw: Hmq Hgetqls Hgettls Hgetq Hin.
    destruct Hw as (pr & msg & sus0 & to & Hgetwait).
    casetac t t0 Het Hnet.
    + subst.
      rewrite Hgett in Hgetwait.
      inverts Hgetwait.
    + do 4 eexists.
      rewrite neq_set_get; eauto.
  - rewrite neq_set_get in Hgetq0; eauto.
    lets Hw: Hmq Hgetqls Hgettls Hgetq0 Hin.
    destruct Hw as (pr & msg & sus0 & to & Hgetwait).
    casetac t t0 Het Hnet.
    + subst.
      rewrite Hgett in Hgetwait.
      inverts Hgetwait.
    + do 4 eexists.
      rewrite neq_set_get; eauto.
Qed.

Lemma qpend_mq_wt_block_update:
  forall O tls qls t p oldmsg sus td q sz ts qd timeout,
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, rdy, oldmsg, sus, td) ->
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq nil sz ts, qd) ->
    td = qd ->
    mq_wt_cond O ->
    mq_wt_cond
      (set
         (set O abstcblsid
            (abstcblist
               (set tls t
                  (p, wait (os_stat_qpend q) (Some timeout), Vnull, sus, td))))
         quelsid (absecblist (set qls q (msgq nil sz (t :: ts), qd)))).
Proof.
  introv Hgettls Hgett Hgetqls Hgetq Heqdom Hmq.
  subst qd.
  unfold mq_wt_cond in *.
  intros qls0 q0 ms0 sz0 ts0 td0 tls0 t0
         Hgetqls0 Hgettls0 Hgetq0 Hin.
  rewrite map_get_set in Hgetqls0.
  rewrite neq_set_get in Hgettls0.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set in Hgettls0.
  inverts Hgetqls0.
  inverts Hgettls0.
  casetac q q0 He Hne.
  - subst.
    rewrite map_get_set in Hgetq0.
    inverts Hgetq0.
    simpl in Hin.
    destruct Hin as [Het | Hin].
    + subst.
      do 4 eexists.
      rewrite map_get_set.
      eauto.
    + lets Hw: Hmq Hgetqls Hgettls Hgetq Hin.
      destruct Hw as (pr & msg & sus0 & to & Hgetwait).
      casetac t t0 Het Hnet.
      * subst.
        rewrite Hgett in Hgetwait.
        inverts Hgetwait.
      * do 4 eexists.
        rewrite neq_set_get; eauto.
  - rewrite neq_set_get in Hgetq0; eauto.
    lets Hw: Hmq Hgetqls Hgettls Hgetq0 Hin.
    destruct Hw as (pr & msg & sus0 & to & Hgetwait).
    casetac t t0 Het Hnet.
    + subst.
      rewrite Hgett in Hgetwait.
      inverts Hgetwait.
    + do 4 eexists.
      rewrite neq_set_get; eauto.
Qed.

Lemma mq_wt_cond_prsv:
  forall O q vl_ ac vl' O' t,
    tsk_mq_same_dom (Vptr q :: vl_) t O ->
    tsk_dom_disj O ->
    que_dom_disj O ->
    mq_wt_cond O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    mq_wt_cond O'.
Proof.
  introv Hsame Htdisj Hqdisj Hmq Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  match goal with
  | Hvl : Vptr q :: vl_ = Vptr _ :: _ |- _ => inverts Hvl
  end.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        unfold tsk_mq_same_dom in Hsame.
        simpl in Hsame.
        destruct Hsame as (d & Hsd & Hqsd).
        assert (Heqdom : x7 = t0).
        {
          assert (Hsdt : sdom_ O t x7).
          {
            left.
            unfold ex_active_tsk.
            do 5 eexists; splits; eauto.
          }
          assert (Hsdq : q_sdom_ O x t0).
          {
            left.
            unfold ex_active_que.
            do 4 eexists; splits; eauto.
          }
          rewrite (Htdisj t x7 d Hsdt Hsd).
          exact (Hqdisj x d t0 Hqsd Hsdq).
        }
        eapply qpend_mq_wt_block_update; eauto.
      * simpljoin.
        eapply qpend_mq_wt_immediate_update; eauto.
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.


Lemma qpend_wt_mq_immediate_update:
  forall O tls qls t p oldmsg sus td q m m0 ms sz ts qd,
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, rdy, oldmsg, sus, td) ->
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq (m0 :: ms) sz ts, qd) ->
    wt_mq_cond O ->
    wt_mq_cond
      (set
         (set O abstcblsid
            (abstcblist (set tls t (p, rdy, m, sus, td))))
         quelsid (absecblist (set qls q (msgq ms sz ts, qd)))).
Proof.
  introv Hgettls Hgett Hgetqls Hgetq Hwt.
  unfold wt_mq_cond in *.
  intros qls0 tls0 t0 pr q0 to msg0 sus0 td0
         Hgettls0 Hgett0 Hgetqls0.
  rewrite neq_set_get in Hgettls0.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set in Hgettls0.
  rewrite map_get_set in Hgetqls0.
  inverts Hgettls0.
  inverts Hgetqls0.
  casetac t t0 He Hne.
  - subst.
    rewrite map_get_set in Hgett0.
    inverts Hgett0.
  - rewrite neq_set_get in Hgett0; eauto.
    lets Hw: Hwt Hgettls Hgett0 Hgetqls.
    destruct Hw as (ms0 & sz0 & ts0 & Hgetq0 & Hin).
    casetac q q0 Heq Hneq.
    + subst.
      pose proof (eq_trans (eq_sym Hgetq) Hgetq0) as Heqv.
      inverts Heqv.
      do 3 eexists.
      split.
      * rewrite map_get_set. eauto.
      * auto.
    + do 3 eexists.
      split.
      * rewrite neq_set_get; eauto.
      * auto.
Qed.

Lemma qpend_wt_mq_block_update:
  forall O tls qls t p oldmsg sus td q sz ts qd timeout,
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, rdy, oldmsg, sus, td) ->
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq nil sz ts, qd) ->
    td = qd ->
    wt_mq_cond O ->
    wt_mq_cond
      (set
         (set O abstcblsid
            (abstcblist
               (set tls t
                  (p, wait (os_stat_qpend q) (Some timeout), Vnull, sus, td))))
         quelsid (absecblist (set qls q (msgq nil sz (t :: ts), qd)))).
Proof.
  introv Hgettls Hgett Hgetqls Hgetq Heqdom Hwt.
  subst qd.
  unfold wt_mq_cond in *.
  intros qls0 tls0 t0 pr q0 to msg0 sus0 td0
         Hgettls0 Hgett0 Hgetqls0.
  rewrite neq_set_get in Hgettls0.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set in Hgettls0.
  rewrite map_get_set in Hgetqls0.
  inverts Hgettls0.
  inverts Hgetqls0.
  casetac t t0 He Hne.
  - subst.
    rewrite map_get_set in Hgett0.
    inverts Hgett0.
    do 3 eexists.
    split.
    + rewrite map_get_set. eauto.
    + simpl. auto.
  - rewrite neq_set_get in Hgett0; eauto.
    lets Hw: Hwt Hgettls Hgett0 Hgetqls.
    destruct Hw as (ms0 & sz0 & ts0 & Hgetq0 & Hin).
    casetac q q0 Heq Hneq.
    + subst.
      pose proof (eq_trans (eq_sym Hgetq) Hgetq0) as Heqv.
      inverts Heqv.
      do 3 eexists.
      split.
      * rewrite map_get_set. eauto.
      * simpl. auto.
    + do 3 eexists.
      split.
      * rewrite neq_set_get; eauto.
      * auto.
Qed.

Lemma mwt_mq_cond_prsv:
  forall O q vl_ ac vl' O' t,
    tsk_mq_same_dom (Vptr q :: vl_) t O ->
    tsk_dom_disj O ->
    que_dom_disj O ->
    wt_mq_cond O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    wt_mq_cond O'.
Proof.
  introv Hsame Htdisj Hqdisj Hwt Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  match goal with
  | Hvl : Vptr q :: vl_ = Vptr _ :: _ |- _ => inverts Hvl
  end.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        unfold tsk_mq_same_dom in Hsame.
        simpl in Hsame.
        destruct Hsame as (d & Hsd & Hqsd).
        assert (Heqdom : x7 = t0).
        {
          assert (Hsdt : sdom_ O t x7).
          {
            left.
            unfold ex_active_tsk.
            do 5 eexists; splits; eauto.
          }
          assert (Hsdq : q_sdom_ O x t0).
          {
            left.
            unfold ex_active_que.
            do 4 eexists; splits; eauto.
          }
          rewrite (Htdisj t x7 d Hsdt Hsd).
          exact (Hqdisj x d t0 Hqsd Hsdq).
        }
        eapply qpend_wt_mq_block_update; eauto.
      * simpljoin.
        tryfalse.
        subst.
        eapply qpend_wt_mq_immediate_update; eauto.
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.

Lemma pend_chs_sat_config_prsv:
  forall O q vl_ ac vl' O' t,
    chs_sat_config O ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    chs_sat_config O'.
Proof.
  introv Hcfg Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        eapply chseq_chs_sat_cfg_prsv; eauto.
        rewrite neq_set_get.
        2: { introv Hf; inverts Hf. }
        rewrite neq_set_get.
        2: { introv Hf; inverts Hf. }
        reflexivity.
      * simpljoin.
        tryfalse.
        subst.
        eapply chseq_chs_sat_cfg_prsv; eauto.
        rewrite neq_set_get.
        2: { introv Hf; inverts Hf. }
        rewrite neq_set_get.
        2: { introv Hf; inverts Hf. }
        reflexivity.
  - unfold err_prop in *.
    simpljoin.
    subst.
    auto.
Qed.

Lemma qpend_before_sched_inv_prsv:
  forall q vl_ t O vl' O' ac
         (Hp : tsk_mq_same_dom (Vptr q :: vl_) t O)
         (Hinv : I O)
         (Hpend : qpend_before_sched t (Vptr q :: vl_) O ac (vl', O')), 
    I O'.
Proof.
  intros.
  inverts Hinv.
  constructors.
  eapply pend_tsk_active_free_disj_prsv; eauto.
  eapply pend_tsk_dom_disj_prsv; eauto.
  eapply pend_tsk_diff_id_prio_prsv; eauto.
  eapply que_active_free_disj_prsv; eauto.
  eapply que_dom_disj_prsv; eauto.
  eapply mq_wt_cond_prsv; eauto.
  eapply mwt_mq_cond_prsv; eauto.
  eapply pend_chs_sat_config_prsv; eauto.
Qed.

Definition qpend_before_schd_post (vl: vallist) (t: tid) (vl': vallist) (O: osabst) :=                
  (exists msg, vl' = Vint32 (Int.repr OS_NO_ERROR) :: msg :: nil) \/
    (exists i, i <> Int.repr OS_NO_ERROR /\ vl' = Vint32 i :: nil). 

Lemma qpend_before_sched_post:
  forall t q vl_ O ac vl' O', 
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') -> 
    qpend_before_schd_post (Vptr q :: vl_) t vl' O'.  
Proof.
  introv Hqbs.
  unfolds in Hqbs.
  simpljoin; tryfalse.
  inverts H.
  d_mt_hyp.
  destruct p.
  destruct q.
  simpljoin.
  -
    d_if_hyp.
    +
      inv_errp.
      unfolds.
      right.
      eexists; splits; eauto.
      introv Hf; inverts Hf.
    +
      d_mt_hyp.
      *
        simpljoin.
        unfolds.
        unfold blocked.
        right; eexists; splits; eauto.
        introv Hf; inverts Hf.
      *
        simpljoin.
        unfolds.
        left; eexists; eauto.
  -
    inv_errp.
    unfolds.
    right.
    eexists; splits; eauto.
    introv Hf; inverts Hf.
Qed.         


Lemma qpend_obsr_equiv_tasks: 
  forall O qls qid sz ts td tls t pr msg sus i v
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq nil sz ts, td))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, rdy, msg, sus, td))
         (Hne : td <> i), 
    obsr_equiv_tasks i O
      (set
         (set O abstcblsid
            (abstcblist (set tls t (pr, wait (os_stat_qpend qid) (Some v), Vnull, sus, td))))
         quelsid (absecblist (set qls qid (msgq nil sz (t :: ts), td)))). 
Proof.
  intros. 
  unfolds.
  split.
  + 
    rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    rewrite map_get_set.
    split.
    * intros. eexists; eauto.
    * intros. simpljoin. inverts H. eexists; eauto.
  +
    introv Hgtls1 Hgtls2.
    rewrite neq_set_get in Hgtls2; eauto; try (introv Hf; inverts Hf).
    rewrite map_get_set in Hgtls2.
    inverts Hgtls2.
    uni_12_sym (get O abstcblsid).
    split.
    *
      split.
      ** introv Hex.
         unfold ex_tsk_in_dom in *.
         destruct Hex as (pr_ & st & m & sus_ & Hgt0).
         casetac t t0 He_ Hne_.
         *** subst.
             uni_12 (get tls t0).
             false.
         *** rewrite neq_set_get; eauto.
      ** introv Hex.
         unfold ex_tsk_in_dom in *.
         destruct Hex as (pr0 & st & m & sus_ & Hgt0).
         casetac t t0 He_ Hne_.
         *** subst.
             rewrite map_get_set in Hgt0.
             inverts Hgt0.
             do 4 eexists; eauto.
         *** rewrite neq_set_get in Hgt0; eauto.
    *
      introv Hgt0 Hgt0' Htd.
      subst d1.
      casetac t t0 He_ Hne_.
      ** subst.
         rewrite map_get_set in Hgt0'.
         inverts Hgt0'.
         uni_12 (get tls t0).
         false.
      ** rewrite neq_set_get in Hgt0'; eauto.
         Set Printing Implicit.
         unfold state.msg in Hgt0.
         rewrite Hgt0 in Hgt0'.
         inverts Hgt0'.
         Unset Printing Implicit. 
         splits; eauto.
Qed.

Lemma qpend_obsr_equiv_mqs:
  forall O qls qid sz ts td tls t pr msg sus i v
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq nil sz ts, td))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, rdy, msg, sus, td))
         (Hne : td <> i), 
    obsr_equiv_mqs i O
      (set
         (set O abstcblsid
            (abstcblist (set tls t (pr, wait (os_stat_qpend qid) (Some v), Vnull, sus, td))))
         quelsid (absecblist (set qls qid (msgq nil sz (t :: ts), td)))). 
Proof.
  intros.
  unfolds.
  split.
  - rewrite map_get_set.
    split.
    + intros. eexists; eauto.
    + introv Hex.
      destruct Hex as (qls0 & Heq).
      inverts Heq.
      eexists; eauto.
  - introv Hgqls1 Hgqls2.
    rewrite map_get_set in Hgqls2.
    inverts Hgqls2.
    uni_12_sym (get O quelsid).
    split.
    +
      unfold ex_mq_in_dom.
      split; introv Hex.
      *
        destruct Hex as (ms & sz_ & ts_ & Hgq_).
        casetac qid q He_ Hne_.
        ** subst.
           uni_12_sym (get qls q).
           false.
        ** rewrite neq_set_get; eauto.
      *
        destruct Hex as (ms & sz0 & ts0 & Hgq_).
        casetac qid q He_ Hne_.
        ** subst.
           rewrite map_get_set in Hgq_.
           inverts Hgq_.
           false.
        ** rewrite neq_set_get in Hgq_; eauto.
    +
      introv Hq1 Hg2 Htd.
      subst d1.
      casetac qid q He_ Hne_.
      * subst.
        uni_12_sym (get qls q).
        false.
      * rewrite neq_set_get in Hg2; eauto.
        uni_12 (get qls q).
        auto.
Qed.             
    
Lemma obsr_equiv_tskd_qpend:
  forall O tls qls qid t sz td pr msg sus ts i v
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq nil sz ts, td))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, rdy, msg, sus, td))
         (Hne : td <> i), 
    obsr_equiv_tskd i O
      (set
         (set O abstcblsid
            (abstcblist (set tls t (pr, wait (os_stat_qpend qid) (Some v), Vnull, sus, td))))
         quelsid (absecblist (set qls qid (msgq nil sz (t :: ts), td)))).
Proof.
  intros.
  constructors.
  -
    eapply qpend_obsr_equiv_tasks; eauto. 
  -
    eapply qpend_obsr_equiv_mqs; eauto.
  -
    apply obsr_equiv_chs_nochange.
    repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
  -
    apply obsr_equiv_fts_nochange.
    repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
  -
    apply obsr_equiv_fqs_nochange.
    repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
Qed.     

Lemma qpend_wt_obsr_equiv_tasks: 
  forall O qls qid m l sz ts tls t pr msg sus td i
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq (m :: l) sz ts, td))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, rdy, msg, sus, td))
         (Hne : td <> i), 
    obsr_equiv_tasks i O
      (set (set O abstcblsid (abstcblist (set tls t (pr, rdy, msg, sus, td)))) quelsid
         (absecblist (set qls qid (msgq l sz ts, td)))). 
Proof.
  intros. 
  unfolds.
  split.
  + 
    rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    rewrite map_get_set.
    split.
    * intros. eexists; eauto.
    * intros. simpljoin. inverts H. eexists; eauto.
  +
    introv Hgtls1 Hgtls2.
    rewrite neq_set_get in Hgtls2; eauto; try (introv Hf; inverts Hf).
    rewrite map_get_set in Hgtls2.
    inverts Hgtls2.
    uni_12_sym (get O abstcblsid).
    split.
    *
      split.
      ** introv Hex.
         unfold ex_tsk_in_dom in *.
         destruct Hex as (pr_ & st & m_ & sus_ & Hgt0).
         casetac t t0 He_ Hne_.
         *** subst.
             uni_12 (get tls t0).
             false.
         *** rewrite neq_set_get; eauto.
      ** introv Hex.
         unfold ex_tsk_in_dom in *.
         destruct Hex as (pr0 & st & m_ & sus_ & Hgt0).
         casetac t t0 He_ Hne_.
         *** subst.
             rewrite map_get_set in Hgt0.
             inverts Hgt0.
             do 4 eexists; eauto.
         *** rewrite neq_set_get in Hgt0; eauto.
    *
      introv Hgt0 Hgt0' Htd.
      subst d1.
      casetac t t0 He_ Hne_.
      ** subst.
         rewrite map_get_set in Hgt0'.
         inverts Hgt0'.
         uni_12 (get tls t0).
         false.
      ** rewrite neq_set_get in Hgt0'; eauto.
         Set Printing Implicit.
         rewrite Hgt0 in Hgt0'.
         inverts Hgt0'.
         Unset Printing Implicit. 
         splits; eauto.
Qed.   

Lemma qpend_mt_obsr_equiv_mqs:
  forall O qls qid m l sz ts td tls t pr msg sus i 
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq (m :: l) sz ts, td))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, rdy, msg, sus, td))
         (Hne : td <> i), 
    obsr_equiv_mqs i O
      (set (set O abstcblsid (abstcblist (set tls t (pr, rdy, msg, sus, td)))) quelsid
         (absecblist (set qls qid (msgq l sz ts, td)))). 
Proof.
  intros.
  unfolds.
  split.
  - rewrite map_get_set.
    split.
    + intros. eexists; eauto.
    + introv Hex.
      destruct Hex as (qls0 & Heq).
      inverts Heq.
      eexists; eauto.
  - introv Hgqls1 Hgqls2.
    rewrite map_get_set in Hgqls2.
    inverts Hgqls2.
    uni_12_sym (get O quelsid).
    split.
    +
      unfold ex_mq_in_dom.
      split; introv Hex.
      *
        destruct Hex as (ms & sz_ & ts_ & Hgq_).
        casetac qid q He_ Hne_.
        ** subst.
           Set Printing Implicit.
           unfold tid in *. unfold qid in *.
           uni_12_sym (get qls q).
           false.
           Unset Printing Implicit.
        ** rewrite neq_set_get; eauto.
      *
        destruct Hex as (ms & sz0 & ts0 & Hgq_).
        casetac qid q He_ Hne_.
        ** subst.
           rewrite map_get_set in Hgq_.
           inverts Hgq_.
           false.
        ** rewrite neq_set_get in Hgq_; eauto.
    +
      introv Hq1 Hg2 Htd.
      subst d1.
      casetac qid q He_ Hne_.
      * subst.
        Set Printing Implicit.
        unfold tid in *. unfold qid in *.
        uni_12_sym (get qls q).
        Unset Printing Implicit. 
        false.
      * rewrite neq_set_get in Hg2; eauto.
        Set Printing Implicit.
        unfold tid in *. unfold Modules.qid in *.
        uni_12 (get qls q).
        Unset Printing Implicit. 
        auto.
Qed. 
  
Lemma obsr_equiv_tskd_qpend_nowt:
  forall (O: osabst) qls qid m l sz ts tls t pr (msg: val) (sus: bool) (td i: task_dom)
         (Hgqls : get O quelsid = Some (absecblist qls))
         (Hgq : get qls qid = Some (msgq (m :: l) sz ts, td))
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, rdy, msg, sus, td))
         (Hne : td <> i), 
    obsr_equiv_tskd i O
      (set (set O abstcblsid (abstcblist (set tls t (pr, rdy, msg, sus, td)))) quelsid
         (absecblist (set qls qid (msgq l sz ts, td)))). 
Proof.
  intros.
  constructors.
  - 
    eapply qpend_wt_obsr_equiv_tasks; eauto.
  -
    eapply qpend_mt_obsr_equiv_mqs; eauto.
  -
    apply obsr_equiv_chs_nochange.
    repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
  -
    apply obsr_equiv_fts_nochange.
    repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
  -
    apply obsr_equiv_fqs_nochange.
    repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
Qed.     

Lemma obsr_euqiv_schd_qpend:
  forall t q vl_ O ac vl' O', 
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') -> 
    obsr_equiv_schd O O'. 
Proof.
  introv Hpend.
  unfolds in Hpend.
  simpljoin.
  d_mt_hyp. 
  -
    destruct p.
    destruct q0.
    simpljoin.
    d_if_hyp.
    + inv_errp.
      eapply dteq_schd_refl; eauto.
    + d_mt_hyp.
      * simpljoin.
        constructors.
        all: repeat rew_neq.
      * simpljoin.
        constructors.
        all: repeat rew_neq.
  -
    inv_errp.
    eapply dteq_schd_refl; eauto.
Qed. 

Lemma qpend_integrity_oblig: 
  forall t O q vl_ ac vl' O' td d
         (Hpre1 : pre1 t O (tsk_mq_same_dom (Vptr q :: vl_)))
         (Hpend : qpend_before_sched t (Vptr q :: vl_) O ac (vl', O'))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d), 
    obsr_equiv_data d O O'.
Proof.
  intros.
  unfolds.
  destruct d.
  -
    unfolds in Hpend.
    destruct Hpend as (qid & v & qls & tls & Heq_ & Hgqls & Hmt).
    inverts Heq_.
    d_mt_hyp.
    + 
      destruct p as (q & tdq).
      destruct q as [ms sz ts].
      destruct Hmt as (Hgtls & Hex).
      destruct Hex as (pr & st & msg0 & sus & td_ & Hgt & Hif).

      d_if_hyp.
      *
        inv_errp.
        apply obsr_equiv_tskd_refl.
      *
        lets Htdeq: tls_sdom_td_eq Hpre1 Hgtls Hgt Hsd.
        subst td_.
        assert (Heqd: tdq = td).
        {
          eapply tq_same_dom_qdom; eauto.
        }
        subst tdq.      
        casetac td i He Hne.
        ** subst. false. apply Hnfl. 
          constructors. 
        ** (* td <> i *) 
          d_mt_hyp.
          ***
            destruct Hif as (HO' & Hac & Hvl').
            subst.
            eapply obsr_equiv_tskd_qpend; eauto.
          ***
            destruct Hif as (Hrdy & HO' & Hac & Hvl').
            subst.
            eapply obsr_equiv_tskd_qpend_nowt; eauto.
    +
      inv_errp.
      apply obsr_equiv_tskd_refl.
  -
    eapply obsr_euqiv_schd_qpend; eauto.
Qed.      


Lemma qpend2_obsr_equiv_tasks:
  forall t O1 O2 qid v' td td' qls1 tls1 qls2 tls2 pr msg sus sz ts
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hdte : obsr_equiv_tskd td O1 O2)
         (Hdte' : obsr_equiv_tskd td' O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr, rdy, msg, sus, td'))
         (Hgq1 : get qls1 qid = Some (msgq nil sz ts, td'))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr, rdy, msg, sus, td'))
         (Hgq2 : get qls2 qid = Some (msgq nil sz ts, td')), 
    obsr_equiv_tasks td
      (set
         (set O1 abstcblsid
            (abstcblist
               (set tls1 t (pr, wait (os_stat_qpend qid) (Some v'), Vnull, sus, td'))))
         quelsid (absecblist (set qls1 qid (msgq nil sz (t :: ts), td'))))
      (set
         (set O2 abstcblsid
            (abstcblist
               (set tls2 t (pr, wait (os_stat_qpend qid) (Some v'), Vnull, sus, td'))))
         quelsid (absecblist (set qls2 qid (msgq nil sz (t :: ts), td')))). 
Proof.
  intros.
  unfold obsr_equiv_tasks.
  split.
  -
    rew_neq. rewrite map_get_set.
    rew_neq. rewrite map_get_set.
    split.
    + intros. eexists; eauto.
    + intros. eexists; eauto.
  -
    introv Hg1 Hg2.
    rew_neq_in Hg1.
    rew_neq_in Hg2.
    rewrite map_get_set in Hg1.
    rewrite map_get_set in Hg2.
    inverts Hg1.
    inverts Hg2.
    split.
    +
      unfold ex_tsk_in_dom.
      casetac t t0 He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split.
        ** introv Hex.
           simpljoin. inverts H.
           do 4 eexists; eauto.
        ** introv Hex.
           simpljoin. inverts H.
           do 4 eexists; eauto.
      * rew_neq.
        rew_neq.
        lets H_: dte_ex_tsk_in_dom_same Hdte; eauto.
    +
      introv Hg1 Hg2.
      casetac t t0 He_ Hne_.
      * subst.
        rewrite map_get_set in Hg1.
        rewrite map_get_set in Hg2.
        inverts Hg1.
        inverts Hg2.
        rename d2 into i.
        intros. subst.
        split; auto.
      * rew_neq_in Hg1.
        rew_neq_in Hg2.
        lets H_: dte_ex_tsk_in_dom_same t0 Hdte.
        specializes H_; eauto.
        assert (Hex2: exists pr0 st m sus0, get tls2 t0 = Some (pr0, st, m, sus0, td)).
        {
          eapply H_; eauto.
        }
        clear H_.
        destruct Hex2 as (pr2_ & st2_ & m2 & sus2_ & Hgt0).
        Set Printing Implicit.
        unfold state.msg in Hgt0.
        rewrite Hg2 in Hgt0.
        Unset Printing Implicit.
        inverts Hgt0.
        eapply obsr_equiv_data_tsk_eq with (td:=td); eauto.
Qed.       


Lemma qpend2_obsr_equiv_mqs:
  forall t O1 O2 qid v' td td' qls1 qls2 tls1 tls2 pr msg sus sz ts 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hdte : obsr_equiv_tskd td O1 O2)
         (Hdte' : obsr_equiv_tskd td' O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr, rdy, msg, sus, td'))
         (Hgq1 : get qls1 qid = Some (msgq nil sz ts, td'))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr, rdy, msg, sus, td'))
         (Hgq2 : get qls2 qid = Some (msgq nil sz ts, td')),  
    obsr_equiv_mqs td
      (set
         (set O1 abstcblsid
            (abstcblist
               (set tls1 t (pr, wait (os_stat_qpend qid) (Some v'), Vnull, sus, td'))))
         quelsid (absecblist (set qls1 qid (msgq nil sz (t :: ts), td'))))
      (set
         (set O2 abstcblsid
            (abstcblist
               (set tls2 t (pr, wait (os_stat_qpend qid) (Some v'), Vnull, sus, td'))))
         quelsid (absecblist (set qls2 qid (msgq nil sz (t :: ts), td')))). 
Proof.
  intros. 
  unfolds.
  split.
  -
    rewrite map_get_set. 
    rewrite map_get_set.
    split; intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    rewrite map_get_set in Hg1.
    inverts Hg1.
    rewrite map_get_set in Hg2.
    inverts Hg2.
    split.
    +
      unfold ex_mq_in_dom.
      casetac qid q He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split.
        ** introv Hex. simpljoin; do 3 eexists; eauto.
        ** introv Hex. simpljoin; do 3 eexists; eauto.
      *
        rew_neq. 
        rew_neq.
        eapply dte_ex_mq_in_dom_same with (td:=td); eauto. 
    +
      introv Hg1 Hg2 Hd.
      casetac qid q He_ Hne_.
      * subst.
        rewrite map_get_set in Hg1.
        rewrite map_get_set in Hg2.
        inverts Hg1.
        inverts Hg2.
        auto.
      * rew_neq_in Hg1.
        rew_neq_in Hg2.
        subst d1.
        lets H_: dte_ex_mq_in_dom_same q Hdte Hgqls1 Hgqls2; eauto.
        assert (Hex2: exists ms sz ts, get qls2 q = Some (msgq ms sz ts, td)).
        {
          eapply H_; eauto.
          destruct mq1.
          do 3 eexists; eauto.
        }
        destruct Hex2 as (ms2 & sz2 & ts2 & Hgq2_).
        assert (d2 = td).
        {
          Set Printing Implicit.
          unfold Modules.qid in Hgq2_.
          rewrite Hg2 in Hgq2_.
          symmetry in Hgq2_.
          Unset Printing Implicit.
          inverts Hgq2_.
          auto.
        }
        subst d2.
        inverts Hdte.
        eapply oe_td_mqs; eauto.
Qed. 
      
Lemma obsr_equiv_tskd_qpend2:
  forall t O1 O2 qid v' td td' qls1 qls2 tls1 tls2 pr msg sus sz ts 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (* (Hsd1 : sdom O1 t td') *)
         (* (Hsd2 : sdom O2 t td') *)
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr, rdy, msg, sus, td'))
         (Hgq1 : get qls1 qid = Some (msgq nil sz ts, td'))
         (* E0 : negb (Int.eq_dec pr (Int.repr OS_IDLE_PRIO)) = false *)
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr, rdy, msg, sus, td'))
         (Hgq2 : get qls2 qid = Some (msgq nil sz ts, td')), 
    obsr_equiv_tskd td
      (set
         (set O1 abstcblsid
            (abstcblist
               (set tls1 t (pr, wait (os_stat_qpend qid) (Some v'), Vnull, sus, td'))))
         quelsid (absecblist (set qls1 qid (msgq nil sz (t :: ts), td'))))
      (set
         (set O2 abstcblsid
            (abstcblist
               (set tls2 t (pr, wait (os_stat_qpend qid) (Some v'), Vnull, sus, td'))))
         quelsid (absecblist (set qls2 qid (msgq nil sz (t :: ts), td')))).
Proof.
  intros.
  simpl in Hdte.
  simpl in Hdte'.
  constructors.
  -
    eapply qpend2_obsr_equiv_tasks; eauto.
  -
    eapply qpend2_obsr_equiv_mqs; eauto.
  -
    match goal with H: _ |- obsr_equiv_chans _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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
    match goal with H: _ |- obsr_equiv_freetids _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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
    match goal with H: _ |- obsr_equiv_freeqids _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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

Lemma qpend2_nowt_obsr_equiv_tasks:
  forall t O1 O2 qid v' td td' qls1 qls2 tls1 tls2 pr msg sus m l sz ts 
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hdte : obsr_equiv_tskd td O1 O2)
         (Hdte' : obsr_equiv_tskd td' O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr, rdy, msg, sus, td'))
         (Hgq1 : get qls1 qid = Some (msgq (m :: l) sz ts, td'))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr, rdy, msg, sus, td'))
         (Hgq2 : get qls2 qid = Some (msgq (m :: l) sz ts, td')), 
    obsr_equiv_tasks td
      (set (set O1 abstcblsid (abstcblist (set tls1 t (pr, rdy, msg, sus, td')))) quelsid
         (absecblist (set qls1 qid (msgq l sz ts, td'))))
      (set (set O2 abstcblsid (abstcblist (set tls2 t (pr, rdy, msg, sus, td')))) quelsid
         (absecblist (set qls2 qid (msgq l sz ts, td')))).
Proof.
  intros.
  unfold obsr_equiv_tasks.
  split.
  -
    rew_neq. rewrite map_get_set.
    rew_neq. rewrite map_get_set.
    split.
    + intros. eexists; eauto.
    + intros. eexists; eauto.
  -
    introv Hg1 Hg2.
    rew_neq_in Hg1.
    rew_neq_in Hg2.
    rewrite map_get_set in Hg1.
    rewrite map_get_set in Hg2.
    inverts Hg1.
    inverts Hg2.
    split.
    +
      unfold ex_tsk_in_dom.
      casetac t t0 He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split.
        ** introv Hex.
           simpljoin. inverts H.
           do 4 eexists; eauto.
        ** introv Hex.
           simpljoin. inverts H.
           do 4 eexists; eauto.
      * rew_neq.
        rew_neq.
        lets H_: dte_ex_tsk_in_dom_same Hdte; eauto.
    +
      introv Hg1 Hg2.
      casetac t t0 He_ Hne_.
      * subst.
        rewrite map_get_set in Hg1.
        rewrite map_get_set in Hg2.
        inverts Hg1.
        inverts Hg2.
        rename d2 into i.
        intros. subst.
        split; auto.
      * rew_neq_in Hg1.
        rew_neq_in Hg2.
        lets H_: dte_ex_tsk_in_dom_same t0 Hdte.
        specializes H_; eauto.
        assert (Hex2: exists pr0 st m sus0, get tls2 t0 = Some (pr0, st, m, sus0, td)).
        {
          eapply H_; eauto.
        }
        clear H_.
        destruct Hex2 as (pr2_ & st2_ & m2 & sus2_ & Hgt0).
        rewrite Hg2 in Hgt0.
        inverts Hgt0.
        eapply obsr_equiv_data_tsk_eq with (td:=td); eauto.
Qed.   

Lemma qpend2_nowt_obsr_equiv_mqs:
  forall t O1 O2 td td' qid v' qls1 qls2 tls1 tls2 pr msg sus m l sz ts
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hdte : obsr_equiv_tskd td O1 O2)
         (Hdte' : obsr_equiv_tskd td' O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr, rdy, msg, sus, td'))
         (Hgq1 : get qls1 qid = Some (msgq (m :: l) sz ts, td'))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr, rdy, msg, sus, td'))
         (Hgq2 : get qls2 qid = Some (msgq (m :: l) sz ts, td')), 
    obsr_equiv_mqs td
      (set (set O1 abstcblsid (abstcblist (set tls1 t (pr, rdy, msg, sus, td')))) quelsid
         (absecblist (set qls1 qid (msgq l sz ts, td'))))
      (set (set O2 abstcblsid (abstcblist (set tls2 t (pr, rdy, msg, sus, td')))) quelsid
         (absecblist (set qls2 qid (msgq l sz ts, td')))). 
Proof. 
  intros. 
  unfolds.
  split.
  -
    rewrite map_get_set. 
    rewrite map_get_set.
    split; intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    rewrite map_get_set in Hg1.
    inverts Hg1.
    rewrite map_get_set in Hg2.
    inverts Hg2.
    split.
    +
      unfold ex_mq_in_dom.
      casetac qid q He Hne.
      * subst.
        do 2 rewrite map_get_set.
        split.
        ** introv Hex. simpljoin; do 3 eexists; eauto.
        ** introv Hex. simpljoin; do 3 eexists; eauto.
      *
        rew_neq. 
        rew_neq.
        eapply dte_ex_mq_in_dom_same with (td:=td); eauto. 
    +
      introv Hg1 Hg2 Hd.
      casetac qid q He_ Hne_.
      * subst.
        rewrite map_get_set in Hg1.
        rewrite map_get_set in Hg2.
        inverts Hg1.
        inverts Hg2.
        auto.
      * rew_neq_in Hg1.
        rew_neq_in Hg2.
        subst d1.
        lets H_: dte_ex_mq_in_dom_same q Hdte Hgqls1 Hgqls2; eauto.
        assert (Hex2: exists ms sz ts, get qls2 q = Some (msgq ms sz ts, td)).
        {
          eapply H_; eauto.
          destruct mq1.
          do 3 eexists; eauto.
        }
        destruct Hex2 as (ms2 & sz2 & ts2 & Hgq2_).
        assert (d2 = td).
        {
          Set Printing Implicit.
          unfold Modules.qid in Hgq2_.
          rewrite Hg2 in Hgq2_.
          symmetry in Hgq2_.
          Unset Printing Implicit.
          inverts Hgq2_.
          auto.
        }
        subst d2.
        inverts Hdte.
        eapply oe_td_mqs; eauto.
Qed.  

Lemma obsr_equiv_tskd_qpend2_nowt:
  forall t O1 O2 qid v' td td' qls1 qls2 tls1 tls2 pr msg sus m l sz ts
         (Hpre11 : pre1 t O1 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hpre12 : pre1 t O2 (tsk_mq_same_dom (Vptr qid :: Vint32 v' :: nil)))
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr, rdy, msg, sus, td'))
         (Hgq1 : get qls1 qid = Some (msgq (m :: l) sz ts, td'))
         (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr, rdy, msg, sus, td'))
         (Hgq2 : get qls2 qid = Some (msgq (m :: l) sz ts, td')), 
    obsr_equiv_tskd td
      (set (set O1 abstcblsid (abstcblist (set tls1 t (pr, rdy, msg, sus, td')))) quelsid
         (absecblist (set qls1 qid (msgq l sz ts, td'))))
      (set (set O2 abstcblsid (abstcblist (set tls2 t (pr, rdy, msg, sus, td')))) quelsid
         (absecblist (set qls2 qid (msgq l sz ts, td')))). 
Proof.
  intros.
  simpl in Hdte.
  simpl in Hdte'.
  constructors.
  -
    eapply qpend2_nowt_obsr_equiv_tasks; eauto.
  -
    eapply qpend2_nowt_obsr_equiv_mqs; eauto.
  -
    match goal with H: _ |- obsr_equiv_chans _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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
    match goal with H: _ |- obsr_equiv_freetids _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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
    match goal with H: _ |- obsr_equiv_freeqids _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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

Lemma qpend_confidentiality_oblig: 
  forall t q vl_ O1 O2 O1' O2' vl1' vl2' ac1 ac2 td 
         (Hpre2 : pre2 t O1 O2 (tsk_mq_same_dom (Vptr q :: vl_)) td obsr_equiv_data flows_to)
         (Hpend1 : qpend_before_sched t (Vptr q :: vl_) O1 ac1 (vl1', O1'))
         (Hpend2 : qpend_before_sched t (Vptr q :: vl_) O2 ac2 (vl2', O2'))
         (Hnex1 : ~ (exists cid, ac1 = _TickAct cid))
         (Hnex2 : ~ (exists cid, ac2 = _TickAct cid)), 
    obsr_equiv_data (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'. 
Proof.
  intros.
  unfolds in Hpre2.
  des_pre2 Hpre2.
  unfolds in Hpend1.
  destruct Hpend1 as (qid1 & v1 & qls1 & tls1 & Heq1_ & Hgqls1 & Hmt1).
  unfolds in Hpend2.
  destruct Hpend2 as (qid2 & v2 & qls2 & tls2 & Heq2_ & Hgqls2 & Hmt2).
  rewrite Heq1_ in Heq2_; inverts Heq2_.
  rename qid2 into qid.
  rename v2 into v'.
  lets H_: dte_mq_cases qid Hgqls1 Hgqls2; eauto.
  d_mt_hyp.
  - destruct p as (q_ & tdq).
    destruct q_ as [ms sz ts].
    Set Printing Implicit.
    unfold tid in E.
    rewrite E in Hmt1.
    Unset Printing Implicit.
    destruct Hmt1 as (Hgtls1 & Hex1).
    destruct Hex1 as (pr1 & st1 & msg1 & sus1 & td1 & Hgt1 & Hif1).
    destruct H_ as [Heqtd | Hneqtd].
    destruct Heqtd as (Heqtd & Hgq2).
    subst tdq.
    assert (Htd1eq: td1 = td').
    {
      eapply tls_sdom_td_eq; eauto.
      apply Hpre11.
    }
    subst td1.
    Set Printing Implicit.
    unfold tid in Hgq2.
    rewrite Hgq2 in Hmt2.
    Unset Printing Implicit.
    destruct Hmt2 as (Hgtls2 & Hex2).
    destruct Hex2 as (pr2 & st2 & msg2 & sus2 & td2 & Hgt2 & Hif2).
    assert (Htd2eq: td2 = td').
    {
      eapply tls_sdom_td_eq; eauto.
      apply Hpre12.
    }
    subst td2.

    lets H_: obsr_equiv_data_tsk_eq Hdte' Hgtls1 Hgtls2 Hgt1 Hgt2; eauto.
    simpljoin.
    rename pr2 into pr.
    rename msg2 into msg.
    rename sus2 into sus.
    
    d_if_hyp.
    + inv_errp. inv_errp.
      splits; eauto.
    +
      destruct ms eqn: Ems.
      * subst ms.
        simpljoin; subst.
        splits; eauto.
        simpl.
        inverts Heq1_.
        lets H_: obsr_equiv_tskd_qpend2 Hpre11 Hpre12 Hdte Hdte'; eauto.
      * subst ms.
        simpljoin; subst.
        splits; eauto.
        simpl.
        inverts Heq1_.
        lets H_: obsr_equiv_tskd_qpend2_nowt Hpre11 Hpre12 Hdte Hdte'; eauto.
    +
      destruct Hneqtd as (Hneqtd & Hmt2_).
      assert (Hqd: q_sdom_ O1 qid tdq).
      { unfolds. left. unfolds. do 4 eexists; splits; eauto. }
      inverts Heq1_.
      lets H_: q_notin_tsk_dom_contra Hpre11 Hsd1 Hneqtd Hqd.
      false. 

  -
    d_mt_hyp.
    *
      destruct p as (q2 & tdq2).
      destruct q2 as [ms2 sz2 ts2].
      assert (Hqd: q_sdom_ O2 qid tdq2).
      { unfolds. left. unfolds. do 4 eexists; splits; eauto. }
      inverts Heq1_.
      lets H__: q_notin_tsk_dom_contra Hpre12 Hsd2 H_ Hqd.
      false.
    *
      Set Printing Implicit.
      unfold tid in E.
      rewrite E in Hmt1.
      unfold tid in E0.
      rewrite E0 in Hmt2.
      Unset Printing Implicit.
      inv_errp.
      inv_errp.
      splits; eauto.

Qed. 

Lemma qpend_ex_active_task_fwd:
  forall O tls qls' p st msg sus td st' msg' t t0 td',
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, msg, sus, td) ->
    ex_active_tsk O t0 td' ->
    ex_active_tsk
      (set
         (set O abstcblsid
            (abstcblist (set tls t (p, st', msg', sus, td))))
         quelsid (absecblist qls')) t0 td'.
Proof.
  introv Hgettls Hgett Hactive.
  unfold ex_active_tsk in *.
  destruct Hactive as
      (tls0 & pr0 & st0 & msg0 & sus0 & Hgettls0 & Hgett0).
  rewrite Hgettls in Hgettls0.
  inverts Hgettls0.
  casetac t t0 He Hne.
  - subst.
    rewrite Hgett in Hgett0.
    inverts Hgett0.
    do 5 eexists.
    split.
    + rewrite neq_set_get.
      2: { introv Hf; inverts Hf. }
      rewrite map_get_set.
      reflexivity.
    + rewrite map_get_set.
      reflexivity.
  - do 5 eexists.
    split.
    + rewrite neq_set_get.
      2: { introv Hf; inverts Hf. }
      rewrite map_get_set.
      reflexivity.
    + rewrite neq_set_get; eauto.
Qed.

Lemma qpend_ex_free_task_fwd:
  forall O tls' qls' t0 td',
    ex_free_tsk O t0 td' ->
    ex_free_tsk
      (set (set O abstcblsid (abstcblist tls'))
           quelsid (absecblist qls')) t0 td'.
Proof.
  introv Hfree.
  unfold ex_free_tsk in *.
  destruct Hfree as (fts & ts & Hgetfts & Hgetts & Hin).
  do 2 eexists.
  splits; eauto.
  rewrite neq_set_get.
  2: { introv Hf; inverts Hf. }
  rewrite neq_set_get.
  2: { introv Hf; inverts Hf. }
  exact Hgetfts.
Qed.

Lemma qpend_sdom_update_iff:
  forall O tls qls' p st msg sus td st' msg' t t0 td',
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, msg, sus, td) ->
    sdom_ O t0 td' <->
    sdom_
      (set
         (set O abstcblsid
            (abstcblist (set tls t (p, st', msg', sus, td))))
         quelsid (absecblist qls')) t0 td'.
Proof.
  introv Hgettls Hgett.
  split; intro Hsd.
  - unfold sdom_ in *.
    destruct Hsd as [Hactive | Hfree].
    + left. eapply qpend_ex_active_task_fwd; eauto.
    + right. eapply qpend_ex_free_task_fwd; eauto.
  - unfold sdom_ in *.
    destruct Hsd as [Hactive | Hfree].
    + left. eapply qpend_ex_active_task_rev; eauto.
    + right. eapply qpend_ex_free_task_rev; eauto.
Qed.

Lemma qpend_before_sched_sdom_iff:
  forall t q vl_ O O' vl' ac,
    pre1 t O (tsk_mq_same_dom (Vptr q :: vl_)) ->
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    forall t0 td, sdom O t0 td <-> sdom O' t0 td.
Proof.
  introv Hpre Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin.
  tryfalse.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp.
    simpljoin.
    tryfalse.
    d_if_hyp.
    + unfold err_prop in *.
      simpljoin.
      subst.
      intros.
      split; auto.
    + simpljoin.
      tryfalse.
      d_mt_hyp.
      * simpljoin.
        tryfalse.
        subst.
        intros.
        eapply qpend_sdom_update_iff; eauto.
      * simpljoin.
        tryfalse.
        subst.
        intros.
        eapply qpend_sdom_update_iff; eauto.
  - unfold err_prop in *.
    simpljoin.
    subst.
    intros.
    split; auto.
Qed.



Lemma qpend_q_sdom_update_iff:
  forall O qls tls' q ms sz ts td ms' ts' q0 td0,
    get O quelsid = Some (absecblist qls) ->
    get qls q = Some (msgq ms sz ts, td) ->
    q_sdom_ O q0 td0 <->
    q_sdom_
      (set (set O abstcblsid (abstcblist tls'))
           quelsid (absecblist (set qls q (msgq ms' sz ts', td))))
      q0 td0.
Proof.
  introv Hgetqls Hgetq.
  split; intro Hsd.
  - unfold q_sdom_ in *.
    destruct Hsd as [Hactive | Hfree].
    + left.
      unfold ex_active_que in *.
      destruct Hactive as
          (qls0 & ms0 & sz0 & ts0 & Hgetqls0 & Hgetq0).
      assert (Heqls : qls0 = qls) by congruence.
      casetac q q0 He Hne.
      * assert (Hsameget : get qls0 q0 = get qls q).
        { rewrite Heqls. rewrite <- He. reflexivity. }
        rewrite Hgetq0 in Hsameget. rewrite Hgetq in Hsameget.
        inverts Hsameget.
        exists (set qls q (msgq ms' sz ts', td)).
        exists ms'. exists sz. exists ts'.
        splits.
        -- rewrite map_get_set. eauto.
        -- rewrite <- He. rewrite map_get_set. eauto.
      * exists (set qls q (msgq ms' sz ts', td)).
        exists ms0. exists sz0. exists ts0.
        splits.
        -- rewrite map_get_set. eauto.
        -- rewrite neq_set_get; eauto.
           rewrite <- Heqls. exact Hgetq0.
    + right.
      unfold ex_free_que in *.
      destruct Hfree as (fqs & qs & Hgetfqs & Hgetqs & Hin).
      do 2 eexists; splits; eauto.
      rewrite neq_set_get.
      2: { introv Hf; inverts Hf. }
      rewrite neq_set_get.
      2: { introv Hf; inverts Hf. }
      exact Hgetfqs.
  - unfold q_sdom_ in *.
    destruct Hsd as [Hactive | Hfree].
    + left. eapply qpend_ex_active_que_rev; eauto.
    + right. eapply qpend_ex_free_que_rev; eauto.
Qed.

Lemma qpend_before_sched_q_sdom_iff:
  forall t q vl_ O O' vl' ac,
    qpend_before_sched t (Vptr q :: vl_) O ac (vl', O') ->
    forall q0 td, q_sdom_ O q0 td <-> q_sdom_ O' q0 td.
Proof.
  introv Hpend.
  unfold qpend_before_sched in Hpend.
  simpljoin; tryfalse.
  d_mt_hyp.
  - destruct p.
    d_mt_hyp; simpljoin; tryfalse.
    d_if_hyp.
    + unfold err_prop in *; simpljoin; subst.
      intros; split; auto.
    + d_mt_hyp; simpljoin; tryfalse; subst; intros;
        eapply qpend_q_sdom_update_iff; eauto.
  - unfold err_prop in *; simpljoin; subst.
    intros; split; auto.
Qed.

Lemma qpend_before_sched_guar:
  forall q vl_ t O vl' O' ac
         (Hp : tsk_mq_same_dom (Vptr q :: vl_) t O)
         (Hinv : I O)
         (Hpend : qpend_before_sched t (Vptr q :: vl_) O ac (vl', O')),
    guar_tsk_env t O O'.
Proof.
  intros.
  unfold guar_tsk_env.
  split.
  - introv Hneq Hsd.
    apply (proj1 (qpend_before_sched_sdom_iff
                    t q vl_ O O' vl' ac (conj Hp Hinv) Hpend t' td)).
    exact Hsd.
  - introv Hqsd.
    apply (proj1 (qpend_before_sched_q_sdom_iff
                    t q vl_ O O' vl' ac Hpend q0 td)).
    exact Hqsd.
Qed.


Lemma dr_qpend_before_schd:
  forall t q vl_,  
    deduct_rules t get_hprio_in_dom (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (tsk_mq_same_dom (Vptr q :: vl_) # qpend_before_sched [|Vptr q :: vl_|])
      (qpend_before_schd_post (Vptr q :: vl_)). 
Proof.
  intros.
  constructors.
  - 
    apply stable_pre_tq_same_d.
  -
    introv Hpre1 Hpend.
    splits.
    + unfolds in Hpre1.
      unfolds.
      destruct Hpre1 as (Hp & Hinv).
      splits.
      * eapply qpend_before_sched_post; eauto.
      * eapply qpend_before_sched_inv_prsv; eauto.
      * eapply qpend_before_sched_guar; eauto. 
    + 
      eapply qpend_before_sched_sdom_iff; eauto.
    +
      introv Htcre.
      unfolds in Hpend; simpljoin; tryfalse.
      d_mt_hyp.
      * destruct p. d_mt_hyp; simpljoin; tryfalse.
        d_if_hyp.
        inverts H3; simpljoin; tryfalse.
        d_mt_hyp; simpljoin; tryfalse.
      * inverts H1; simpljoin; tryfalse.
    +
      introv Hnex Hsd Hnfl.
      eapply qpend_integrity_oblig; eauto.      
  -
    introv Hpre2 Hpend1 Hpend2 Hnex1 Hnex2.    
    eapply qpend_confidentiality_oblig; eauto.    
Qed.

Lemma qpend_after_sched_sdom_eq:
  forall t O ac vl' O', 
    qpend_after_sched t nil O ac (vl', O') ->
    (forall t' td, sdom_ O t' td <-> sdom_ O' t' td). 
Proof.
  introv Hpend.
  inverts Hpend.
  destruct H as (pr & st & m & su & td & Hgtls & Hgt & Hmt).
  assert (Hor: (exists a, m = Vptr a) \/ (~exists a, m = Vptr a)) by tauto.
  destruct Hor as [Hptr | Hnptr].
  - destruct Hptr as (a & Hm).
    subst m.
    simpljoin. 
    intros.
    split.
    + 
      introv Hsd.
      unfold sdom_ in *.
      destruct Hsd as [Heat | Heft].
      **
        left. 
        eapply ex_active_tsk_set_t_prsv with (O:=O); eauto.
      **
        right. 
        eapply same_tsks_ex_free_tsk with (O:=O); eauto.
        rew_neq. 
    +
      introv Hsd.
      unfold sdom_ in *.
      destruct Hsd as [Heat | Heft].
      **
        left.
        
        eapply ex_active_tsk_set_t_prsv_rev in Heat; eauto.
      **
        right.
        eapply same_tsks_ex_free_tsk with
          (O:=set O abstcblsid (abstcblist (set x t (pr, st, Vnull, su, td)))); eauto.
        rew_neq.
  -
    assert (vl' = Vnull :: nil /\ O' = O /\ ac = _TauAct).
    {
      destruct m; auto.
      false. apply Hnptr; eexists; eauto.
    }
    simpljoin.
    intros.
    tauto.
Qed. 

Lemma qpend_after_sched_q_sdom_impl:
  forall t O ac vl' O', 
    qpend_after_sched t nil O ac (vl', O') ->
    forall (q : qid) (td : task_dom), q_sdom_ O q td -> q_sdom_ O' q td.
Proof.
  introv Hpend Hsd.
  inverts Hpend.
  destruct H as (pr & st & m & su & td_ & Hgtls & Hgt & Hmt).
  unfold q_sdom_ in *.
  assert (Hor: (exists a, m = Vptr a) \/ (~exists a, m = Vptr a)) by tauto.
  destruct Hor as [Hptr | Hnptr].
  - destruct Hptr as (a & Hm).
    subst m.
    simpljoin. 
    destruct Hsd as [Heaq | Hefq].
    + left.
      eapply same_mqs_ex_active_que with (O:=O); eauto.
      rew_neq.
    + right.
      eapply same_mqs_ex_free_que with (O:=O); eauto.
      rew_neq.
  - assert(vl' = Vnull :: nil /\ O' = O /\ ac = _TauAct).
    {
      destruct m; auto.
      false. apply Hnptr; eexists; eauto.
    }
    simpljoin.
    auto.
Qed. 

Lemma pend_after_sched_guar:
  forall t O ac vl' O', 
    qpend_after_sched t nil O ac (vl', O') -> 
    guar_tsk_env t O O'. 
Proof.
  introv Hpend.
  unfolds.
  split.
  - 
    introv Hneq Hsd.
    lets H_: qpend_after_sched_sdom_eq Hpend.
    eapply H_; eauto.
  -
    eapply qpend_after_sched_q_sdom_impl; eauto.
Qed. 

Lemma upd_tsk_obsr_equiv_tasks: 
  forall O tls t tsk tsk' td td', 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some tsk ->
    snd tsk = td -> 
    snd tsk' = td ->    
    ~flows_to (TaskDom td) (TaskDom td') -> 
    obsr_equiv_tasks td' O (set O abstcblsid (abstcblist (set tls t tsk'))). 
Proof.
  introv Hgtls Hgt Htd Htd_ Hnfl.
  casetac td td' He Hne.
  - subst.
    false.
    apply Hnfl.
    constructors.
  - clear Hnfl.
    unfold obsr_equiv_tasks.
    destruct tsk as [[[[]]]].
    destruct tsk' as [[[[]]]].
    simpl in Htd. simpl in Htd_.
    subst. 
    split.
    + rewrite map_get_set.
      split; intros; eexists; eauto.
    + introv Hg1 Hg2.
      rewrite map_get_set in Hg2.
      inverts Hg2.
      rewrite Hgtls in Hg1.
      symmetry in Hg1.
      inverts Hg1.
      split.
      * unfold ex_tsk_in_dom.
        casetac t t1 He_ Hne_.
        ** subst. rewrite map_get_set.
           rewrite Hgt.
           split.
           *** intros. simpljoin. inverts H. do 4 eexists; eauto.
           *** intros. simpljoin. inverts H. do 4 eexists; eauto.
        ** rew_neq.
           tauto.
      *
        introv Hg1 Hg2.
        casetac t t1 He_ Hne_.
        ** subst.
           rewrite map_get_set in Hg2.
           inverts Hg2.
           uni_21_sym (get tls t1).
           introv Hd.
           false.
        ** rew_neq_in Hg2.
           uni_21 (get tls t1).
           splits; eauto.
Qed.

Lemma qpend_asch_integrity_oblig:
  forall t O ac vl' O' td d
         (Hpre1 : pre1 t O trivial_asrt)
         (Hpas : qpend_after_sched t nil O ac (vl', O'))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d), 
    obsr_equiv_data d O O'.
Proof.
  intros.
  unfolds.
  destruct d.
  -
    unfolds in Hpas. 
    destruct Hpas as (tls & pr & st & m & su & td_ & Hgtls & Hgt & Hmt). 
    d_mt_hyp; try (simpljoin; apply obsr_equiv_tskd_refl; fail).

    subst m.
    simpljoin.
    constructors.
    +  
      lets H_: tls_sdom_td_eq Hpre1 Hgtls Hgt Hsd; eauto.
      subst td_.
      eapply upd_tsk_obsr_equiv_tasks; eauto.
    +
      eapply obsr_equiv_mqs_nochange; eauto.
      rew_neq.
    +
      eapply obsr_equiv_chs_nochange; eauto.
      rew_neq.
    +
      eapply obsr_equiv_fts_nochange; eauto.
      rew_neq.
    +
      eapply obsr_equiv_fqs_nochange; eauto.
      rew_neq.
  -
    unfolds in Hpas. 
    destruct Hpas as (tls & pr & st & m & su & td_ & Hgtls & Hgt & Hmt).
    d_mt_hyp; try (simpljoin; apply dteq_schd_refl; fail).
    simpljoin.
    constructors; try rew_neq.
Qed. 


Lemma upd_tsk2_obsr_equiv_tasks:
  forall td O1 O2 td' tls1 tls2 t tsk tsk' 
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt1 : get tls1 t = Some tsk)
         (Hgt2 : get tls2 t = Some tsk)
         (Hsd: snd tsk = td')
         (Hsd': snd tsk' = td'), 
    obsr_equiv_tasks td
      (set O1 abstcblsid (abstcblist (set tls1 t tsk')))
      (set O2 abstcblsid (abstcblist (set tls2 t tsk'))). 
Proof.
  intros.
  destruct tsk as [[[[]]]].
  destruct tsk' as [[[[]]]].
  simpl in Hsd.
  simpl in Hsd'.
  subst.
  simpl in Hdte.
  simpl in Hdte'.
  unfolds.
  split.
  - do 2 rewrite map_get_set. 
    split; intros; eexists; eauto.
  - introv Hg1 Hg2.
    rename tls0 into tls1'.
    rename tls3 into tls2'.
    rewrite map_get_set in Hg1. 
    rewrite map_get_set in Hg2.
    inverts Hg1.
    inverts Hg2.
    rename t1 into t'.
    casetac t t' He Hne.
    +
      subst. 
      split.
      * 
        unfold ex_tsk_in_dom.
        do 2 rewrite map_get_set.
        split; introv Hex; simpljoin; do 4 eexists; eauto.
      *
        do 2 rewrite map_get_set.
        introv Hg1 Hg2 Hd.
        inverts Hg1. inverts Hg2.
        splits; eauto.
    +
      repeat rew_neq.
      split.
      * unfold ex_tsk_in_dom.
        do 2 rew_neq.
        lets H__: dte_ex_tsk_in_dom_same t' Hdte Hgtls1 Hgtls2.
        auto.
      * introv Hg1 Hg2 Hd.
        subst d1.
        lets H__: dte_ex_tsk_in_dom_same t' Hdte Hgtls1 Hgtls2.
        assert (Hex: exists pr0 st m sus0, get tls1 t' = Some (pr0, st, m, sus0, td)).
        {
          do 4 eexists; eauto.
        }
        eapply H__ in Hex.
        destruct Hex as (pr0 & st0 & Hm0 & sus0 & Hgt2').
        assert (d2 = td).
        {
          uni_12 (get tls2 t'). auto.
        }
        subst d2.
        clear Hgt2'.
        eapply obsr_equiv_data_tsk_eq with (td:=td); eauto.
Qed.
    
Lemma qpend_asch_confidentiality_oblig:
  forall t O1 O2 ac1 ac2 vl1' vl2' O1' O2' td
         (Hpre2 : pre2 t O1 O2 trivial_asrt td obsr_equiv_data flows_to)
         (Hpa1 : qpend_after_sched t nil O1 ac1 (vl1', O1'))
         (Hpa2 : qpend_after_sched t nil O2 ac2 (vl2', O2')), 
    obsr_equiv_data (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'. 
Proof.
  intros.
  des_pre2 Hpre2.
  unfolds in Hpa1.
  unfolds in Hpa2.
  destruct Hpa1 as (tls1 & pr1 & st1 & m1 & su1 & td1_ & Hgtls1 & Hgt1 & Hmt1).
  destruct Hpa2 as (tls2 & pr2 & st2 & m2 & su2 & td2_ & Hgtls2 & Hgt2 & Hmt2).
  lets H1_: tls_sdom_td_eq Hpre11 Hgtls1 Hgt1 Hsd1.
  lets H2_: tls_sdom_td_eq Hpre12 Hgtls2 Hgt2 Hsd2.
  subst td1_. subst td2_.
  lets H__: obsr_equiv_data_tsk_eq Hdte' Hgtls1 Hgtls2 Hgt1 Hgt2.
  simpljoin.
  rename m2 into m.
  rename pr2 into pr. rename st2 into st. rename su2 into su.
  destruct m; simpljoin; try splits; eauto.
  constructors.
  -
    eapply upd_tsk2_obsr_equiv_tasks with (O1:=O1) (O2:=O2); eauto.
  -
    match goal with H: _ |- _ _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
    assert (H1_1: obsr_equiv_mqs td O1_ O1).
    {
      eapply obsr_equiv_mqs_nochange; eauto.
      subst O1_.
      repeat rew_neq.
    }
    assert (H22_: obsr_equiv_mqs td O2 O2_).
    {
      eapply obsr_equiv_mqs_nochange; eauto.
      subst O2_.
      repeat rew_neq.
    }
    eapply dteq_mqs_trans with (O2:=O2); eauto.
    inverts Hdte.
    eapply dteq_mqs_trans with (O2:=O1); eauto.
  -
    match goal with H: _ |- obsr_equiv_chans _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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
    match goal with H: _ |- obsr_equiv_freetids _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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
    match goal with H: _ |- obsr_equiv_freeqids _ ?O1 ?O2 => set (O1_:=O1); set (O2_:=O2) end.
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


Lemma qpend_after_sched_inv_prsv:
  forall t O ac vl' O',
    I O ->
    qpend_after_sched t nil O ac (vl', O') ->
    I O'.
Proof.
  introv Hinv Hpend.
  unfold qpend_after_sched in Hpend.
  destruct Hpend as (tls & pr & st & msg & sus & td & Hgtls & Hgt & Hmsg).
  destruct msg; simpl in Hmsg; simpljoin; subst; try exact Hinv.
  destruct Hinv as [Htaf Htdisj Hdiff Hqaf Hqdisj Hmq Hwt Hch].
  constructors.
  - unfold tsk_active_free_disj in *.
    introv Hactive Hfree.
    eapply Htaf.
    + eapply ex_active_tsk_set_t_prsv_rev with
          (tls:=tls) (tsk:=(pr, st, Vptr a, sus, td))
          (tsk':=(pr, st, Vnull, sus, td)) (td:=td); simpl; eauto.
    + unfold ex_free_tsk in *.
      destruct Hfree as (fts & ts & Hfts & Hg & Hin).
      rewrite neq_set_get in Hfts.
      2: { introv Hf; inverts Hf. }
      do 2 eexists; splits; eauto.
  - unfold tsk_dom_disj in *.
    introv Hsd1 Hsd2.
    assert (Hrev: forall t' td',
               sdom_ (set O abstcblsid
                        (abstcblist (set tls t (pr, st, Vnull, sus, td))))
                 t' td' -> sdom_ O t' td').
    {
      introv Hsd.
      unfold sdom_ in *.
      destruct Hsd as [Hactive | Hfree].
      - left. eapply ex_active_tsk_set_t_prsv_rev with
            (tls:=tls) (tsk:=(pr, st, Vptr a, sus, td))
            (tsk':=(pr, st, Vnull, sus, td)) (td:=td); simpl; eauto.
      - right.
        unfold ex_free_tsk in *.
        destruct Hfree as (fts & ts & Hfts & Hg & Hin).
        rewrite neq_set_get in Hfts.
        2: { introv Hf; inverts Hf. }
        do 2 eexists; splits; eauto.
    }
    eapply Htdisj; eauto.
  - unfold tsk_diff_id_prio in *.
    rewrite map_get_set.
    introv Heqtls Hneq Hg1 Hg2. inverts Heqtls.
    casetac t t1 He1 Hne1.
    + subst. rewrite map_get_set in Hg1. inverts Hg1.
      rewrite neq_set_get in Hg2; eauto.
    + rewrite neq_set_get in Hg1; eauto.
      casetac t t2 He2 Hne2.
      * subst. rewrite map_get_set in Hg2. inverts Hg2. eauto.
      * rewrite neq_set_get in Hg2; eauto.
  - eapply same_mqs_que_active_free_disj with (O:=O); eauto;
      try (rewrite neq_set_get; eauto; introv Hf; inverts Hf).
  - eapply same_mqs_que_dom_disj with (O:=O); eauto;
      try (rewrite neq_set_get; eauto; introv Hf; inverts Hf).
  - unfold mq_wt_cond in *.
    intros qls0 q0 ms0 sz0 ts0 td0 tls0 t0
           Hgqls Hgtls' Hgq Hin.
    pose proof Hgqls as Hgqls_old.
    rewrite neq_set_get in Hgqls_old.
    2: { introv Hf; inverts Hf. }
    pose proof (Hmq qls0 q0 ms0 sz0 ts0 td0 tls t0
                    Hgqls_old Hgtls Hgq Hin) as Hw.
    rewrite map_get_set in Hgtls'.
    assert (Htls0:
              tls0 = set tls t (pr, st, Vnull, sus, td)) by congruence.
    destruct Hw as [pr0 [msg0 [sus0 [to Hwait]]]].
    casetac t t0 He Hne.
    + inverts He.
      assert (Hsame:
                Some (pr, st, Vptr a, sus, td) =
                Some (pr0, wait (os_stat_qpend q0) to, msg0, sus0, td0)).
      { transitivity (get tls t0); [symmetry; eauto | eauto]. }
      inverts Hsame.
      do 4 eexists. rewrite Htls0. rewrite map_get_set. reflexivity.
    + do 4 eexists. rewrite Htls0. rewrite neq_set_get; eauto.
  - unfold wt_mq_cond in *.
    introv Hgtls' Hwait Hgqls.
    pose proof Hgtls as Hgtls_old.
    pose proof Hgqls as Hgqls_old.
    rewrite neq_set_get in Hgqls_old.
    2: { introv Hf; inverts Hf. }
    rewrite map_get_set in Hgtls'. inverts Hgtls'.
    casetac t t0 He Hne.
    + inverts He. rewrite map_get_set in Hwait. inverts Hwait.
      eapply Hwt; eauto using Hgtls_old, Hgqls_old.
    + rewrite neq_set_get in Hwait; eauto.
  - eapply same_chs_chs_sat_config with (O:=O); eauto.
    rewrite neq_set_get; eauto. introv Hf; inverts Hf.
Qed.


Lemma dr_qpend:
  forall vl t, 
    tl_vl_match (Tptr Tvoid :: Tint16 :: nil) vl = true -> 
    deduct_rules t get_hprio_in_dom (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (mq_apispecs.qpend vl) q_star.
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
    destruct vl0.
    + 
      introv Hs2.
      subst s2.
      split.
      * apply ssp_end.
      * constructors.
    +
      destruct Hq as (Hi & Hpost).
      destruct Hi as (i &Heq); inverts Heq. 
      introv Hv.
      assert (Hor: (exists vl_, vl = Vnull :: vl_) \/ exists q vl_, vl = Vptr q :: vl_).
      {
        destruct vl; simpl in Htvm; tryfalse.
        destruct v; simpl in Htvm; tryfalse.
        left. eexists; eauto.
        right. do 2 eexists; eauto.
      }
      
      d_if_hyp.
      * (* dom_chk_ok *)
        subst.
        split.
        **
          assert (i = dom_chk_ok).
          {
            pose proof Int.eq_spec.
            specialize (H i dom_chk_ok).
            rewrite E in H.
            auto.
          }
          subst i.
          specialize (Hpost (eq_refl _)).
          unfolds.
          simpl.
          unfolds.
          destruct Hor as [Hnull | Hnn].
          ***
            simpljoin.
          ***
            simpljoin.
            specializes Hpost; eauto.
        **
          destruct Hor.
          *** (* q ptr is NULL *)
            simpljoin; subst.
            constructors.
            ****
              instantiate (1:=q_bot).
              constructors.
              ***** 
                unfold tsk_mq_same_dom. apply stable_pre_trivial_asrt.
              *****
                introv Hpre1 Hpbs. inverts Hpbs. simpljoin; tryfalse.
              *****
                introv Hpre2 Hpend1 Hpend2. inverts Hpend1; simpljoin; tryfalse.
            ****
              introv Hinv0 Hq.
              unfolds in Hq. false. 
          ***
            destruct H as (q & vl_ & Hvl).
            eapply seq_rule with (q':=qpend_before_schd_post (Vptr q :: vl_)).
            {
              subst vl.
              apply dr_qpend_before_schd.
            }
            {
              introv Hinv0 Hpost_ Hvl0.
              clear Hpost.
              d_mt_hyp; subst s2.
              -
                split.
                + simpl. unfolds; auto.
                + apply dr_ssp.
              -
                unfolds in Hpost_.
                destruct v; destruct Hpost_; simpljoin; tryfalse.
                +
                  inverts H.
                  change (Int.eq (Int.repr OS_NO_ERROR) Int.zero) with true.
                  simpl.
                  split.
                  *
                    unfolds. auto.
                  *
                    constructors.
                +
                  inverts H0.
                  asserts_rewrite (Int.eq x Int.zero = false).
                  { 
                    eapply Int.eq_false; eauto.
                  }
                  destruct (Int.eq x Int.mone) eqn: E1.
                  * 
                    split.
                    ** simpl. unfolds; auto.
                    **
                      constructors.
                      { (* sched *) 
                        instantiate (1:=q_star).
                        apply dr_sched.
                      }
                      { (* qpend_after_sched *)  
                        introv Hinv_ Hq Hs2.
                        subst s2.
                        split.
                        - simpl. unfolds; auto.
                        - constructors.
                          + apply stable_pre_trivial_asrt.
                          + introv Hpre1 Hpas.
                            split.
                            unfolds.
                            splits.
                            * unfolds; auto.
                            * unfolds in Hpre1.
                              destruct Hpre1.
                              eapply qpend_after_sched_inv_prsv; eauto.
                            * eapply pend_after_sched_guar; eauto.
                            * splits.
                              ** unfold sdom. unfold state.
                                 intros. eapply qpend_after_sched_sdom_eq; eauto.
                              ** introv Hac. inverts Hpas; simpljoin.
                                 d_mt_hyp; simpljoin; tryfalse. 
                              ** (* integrity oblig. *)    
                                introv Hntck Hsd Hnfl.
                                eapply qpend_asch_integrity_oblig; eauto.
                                 
                          + (* confidentiality oblig. *)
                            introv Hpre2 Hpa1 Hpa2 Hnex1 Hnex2.     
                            eapply qpend_asch_confidentiality_oblig; eauto.
                      }
                  *
                    split.
                    ** apply ssp_end.
                    ** constructors. 
            }

      * (* dom_chk_err *)
        subst s2.
        split.
        ** apply ssp_end.
        ** constructors.
Qed. 

    
