
Require Import LibTactics.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import state.
Require Import rules.

Require Import join_lib.
Require Import int_auto.
Require Import my_tacs.

Require Import specs_common.
Require Import tick_spec. 
Require Import obsr_equiv.

Require Import dteq_props.
Require Import aux_lemmas.
Require Import inv_props.

(* Lemma scheq_dsch_data_valid_prsv: *)
(*   forall O O', *)
(*     dsch_data_valid O ->  *)
(*     get O dschedlenid = get O' dschedlenid -> *)
(*     get O dschedidxid = get O' dschedidxid -> *)
(*     get O dschedid  = get O' dschedid -> *)
(*     dsch_data_valid O'.  *)
(* Proof.  *)
(*   introv Hddv Hgeq1 Hgeq2 Hgeq3. *)
(*   inverts Hddv. *)
(*   constructors. *)
(*   - intros. *)
(*     rewrite <- Hgeq1 in H. *)
(*     eapply dv_len_rgn; eauto. *)
(*   - intros. *)
(*     rewrite <- Hgeq1 in H. *)
(*     rewrite <- Hgeq2 in H1. *)
(*     eapply dv_idx_rgn; eauto. *)
(*   - intros. *)
(*     rewrite <- Hgeq1 in H. *)
(*     rewrite <- Hgeq3 in H1. *)
(*     eapply dv_tbl_valid; eauto. *)
(* Qed.      *)

Lemma sub_get_same:
  forall (m m': TcbMod.map) x a, 
    get m x = Some a -> 
    Maps.sub m m' ->
    get m' x = Some a. 
Proof.
  intros.
  unfold Maps.sub in *.
  destruct H0 as (x' & Hjo).
  jeat.
Qed. 

Lemma tickstep1_dteq_preserved:
  forall cd tls tls' qls qls' tls0, 
    tickstep' cd tls qls tls' qls' tls0 ->
    Maps.sub tls0 tls -> 
    forall td O O', 
      cd <> td -> 
      I O -> 
      get O abstcblsid = Some (abstcblist tls) ->
      get O quelsid = Some (absecblist qls) ->
      get O' abstcblsid = Some (abstcblist tls') ->
      get O' quelsid = Some (absecblist qls') ->
      (obsr_equiv_tasks td O O' /\ obsr_equiv_mqs td O O'). 
Proof.
  introv Hstep'.
  induction Hstep';
    introv Hsub Hneq Hinv Hgtls Hgqls Hgtls' Hgqls'.
  
  -
    split.
    + eapply obsr_equiv_tasks_nochange; eauto.
      congruence.
    + eapply obsr_equiv_mqs_nochange; eauto.
      congruence.
      
  -
    rename O' into O''.
    assert (Hsub': Maps.sub tls_used' tls').
    {
      eapply sub_join_set_sub; eauto.
    }
    
    specialize (IHHstep' Hsub' td0
                  (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) O'').
    rewrite Hgqls' in IHHstep'.
    rewrite Hgtls' in IHHstep'.
    rewrite map_get_set in IHHstep'.
    rewrite neq_set_get in IHHstep'; eauto.
    2: { introv Hf; inverts Hf. }
    rewrite map_get_set in IHHstep'.
    assert (Hgtu: get tls_used t = Some (p, st, msg0, sus0, td)) by jeat.
    assert (Hinv': I (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls'))).
    {
      eapply tickchange_prsv_inv; eauto.
      unfolds in Hsub.
      simpljoin.
      clear -H2 Hgtu.
      eapply join_get_l; eauto.
    }
    specialize (IHHstep' Hneq Hinv' (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _)).
    destruct IHHstep' as (Hdteq_t' & Hdteq_q').
    
    assert (Heqt0: obsr_equiv_tasks td0
                     O (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls'))).
    {
      unfolds.
      rewrite neq_set_get; eauto. 2: introv Hf; inverts Hf.
      rewrite map_get_set.
      split.
      - split; intros; eexists; eauto.
      - introv Hg1 Hg2.
        inverts Hg2.
        rewrite Hgtls in Hg1. inverts Hg1.
        assert (Hgt1: get tls1 t = Some (p, st, msg0, sus0, td)).
        {
          eapply map_tactics.sub_get_get; eauto.
        }
        assert (Hgt2: get tls2 t = Some (p, st', msg0, sus0, td)).
        {
          subst tls2. rewrite map_get_set. auto.
        }
        split.
        +
          unfold ex_tsk_in_dom.
          casetac t t0 He Hne.
          *
            subst.
            rewrite map_get_set.
            split.
            ** introv Hg1.
               destruct Hg1 as (pr1 & st1 & m1 & sus1 & Hgt1_).
               unfold tidspec.A in Hgt1.
               rewrite Hgt1 in Hgt1_.
               inverts Hgt1_. do 4 eexists; eauto.
            ** introv Hg2.
               destruct Hg2 as (pr2 & st2 & m2 & sus2 & Heq2).
               inverts Heq2.
               do 4 eexists; eauto.
          *
            subst tls2.
            rewrite neq_set_get; eauto.
            tauto.
        +
          subst tls2.
          casetac t t0 He Hne.
          *
            subst.
            rewrite map_get_set.
            introv Hgt1_ Hgt2_ Hd.
            inverts Hgt2_.
            unfold tidspec.A in Hgt1.
            rewrite Hgt1 in Hgt1_.
            inverts Hgt1_.
            false.
          *
            rewrite neq_set_get; eauto.
            introv Hgt1_ Hgt2_ Hd.
            Set Printing Implicit.
            unfold tidspec.A in Hgt2_.
            rewrite Hgt1_ in Hgt2_.
            inverts Hgt2_.
            splits; auto.
            Unset Printing Implicit.
    }

    lets Hqls': tickchange_inversion H0.

    assert (Heqq0: obsr_equiv_mqs td0 O
                     (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls'))).
    {
      clear Heqt0.
      unfolds.
      rewrite map_get_set. 
      split.
      - split; eexists; eauto.
      - introv Hg1 Hg2.
        inverts Hg2.
        destruct Hqls' as [Heq | Hex].
        + subst.                  
          rewrite Hgqls in Hg1.
          inverts Hg1.
          split.
          * tauto.
          * introv Hgq1 Hgq2 Hd.
            rewrite Hgq1 in Hgq2. inverts Hgq2.
            auto.
        + destruct Hex as (qid0 & d0 & ms & sz & ts & Hst & Hget & Hqls2).
          subst st.
          rewrite Hgqls in Hg1.
          inverts Hg1.
          split.
          *
            unfold ex_mq_in_dom.
            subst qls2.
            casetac qid0 q He Hne.
            ** subst. rewrite map_get_set.
               split.
               ***
                 introv Hg. destruct Hg as (ms0 & sz0 & ts0 &  Hgq0).
                 rewrite Hget in Hgq0.
                 inverts Hgq0.
                 do 3 eexists; eauto.
               ***
                 introv Hsomeq.
                 destruct Hsomeq as (ms0 & sz0 & ts0 & Hseq).
                 inverts Hseq.
                 do 3 eexists; eauto.
            **
              rewrite neq_set_get; eauto.
              tauto.
          *
            introv Hg1 Hg2 Hgd.
            casetac q qid0 He Hne.
            ** subst.
               inverts Hinv.
               assert (Hgtls_: get tls t = Some (p, wait (os_stat_qpend qid0) (Some Int.one), msg0, sus0, td)).
               {
                 clear -Hsub Hgtu.
                 eapply sub_get_same; eauto.
               }
               unfolds in inv_wt_mq.
               lets H__: inv_wt_mq Hgtls Hgtls_ Hgqls.
               destruct H__ as (ms0 & sz0 & ts0 & Hget0).
               rewrite Hg1 in Hget0.
               simpljoin.
               false. 

            ** rewrite Hqls2 in Hg2.
               rewrite neq_set_get in Hg2; eauto.
               congruence. 
    }
    
    split.
    +
      eapply dteq_tasks_trans; eauto.
    +
      eapply dteq_mqs_trans; eauto.
  -
    eapply IHHstep'; eauto.
    assert (Maps.sub tls_used' tls_used).
    {
      clear -H.
      eapply join_sub_r; eauto.
    }
    eapply sub_trans; eauto.
Qed.

Definition tls_equiv td tls1 tls2 :=
  forall t, 
    (ex_tsk_in_dom t td tls1 <-> ex_tsk_in_dom t td tls2) /\
      (forall (pr1 pr2 : priority) (st1 st2 : taskstatus) (msg1 msg2 : msg)
              (sus1 sus2 : sus_st) (d1 d2 : task_dom),
          get tls1 t = Some (pr1, st1, msg1, sus1, d1) ->
          get tls2 t = Some (pr2, st2, msg2, sus2, d2) ->
          d1 = td -> pr1 = pr2 /\ st1 = st2 /\ msg1 = msg2 /\ sus1 = sus2). 

Lemma tls_equiv_emp:
  forall tls td, tls_equiv td emp tls -> (forall t, ~ex_tsk_in_dom t td tls).
Proof.
  introv Hte Hex.      
  unfolds in Hte.
  specialize (Hte t).
  destruct Hte as (Heqv & Hall).
  eapply Heqv in Hex; eauto.
  unfolds in Hex.
  simpljoin; auto.
  rewrite map_emp_get in H.
  false. 
Qed. 

Lemma not_ex_t_indom_tickstep'_nochange:
  forall td tls qls tls' qls' tls0, 
    tickstep' td tls qls tls' qls' tls0 -> 
    (forall t, ~ex_tsk_in_dom t td tls0) ->
    tls = tls' /\ qls = qls'.
Proof.
  introv Hstep'.
  induction Hstep'; introv Hnex.
  - split; auto.
  -
    assert (ex_tsk_in_dom t td tls_used).
    {
      assert (Hgtu: get tls_used t = Some (p, st, msg0, sus0, td)).
      {
        jeat.
      }
      unfolds.
      do 4 eexists; eauto.
    }
    false. 
    eapply Hnex in H2; eauto.
  -
    assert (Hnex': (forall t, ~ex_tsk_in_dom t td tls_used')).
    {
      introv Hex.
      specialize (Hnex t0).
      apply Hnex.
      unfold ex_tsk_in_dom.
      unfold ex_tsk_in_dom in Hex.
      destruct Hex as (pr & st_ & m & sus & Hgt).
      do 4 eexists.
      eapply join_get_r; eauto.
    }
    eapply IHHstep' in Hnex'; eauto.
Qed. 

Lemma joinsig_eq: 
  forall (tls1' tls2' tls: TcbMod.map) t tsk1 tsk2,
    joinsig t tsk1 tls1' tls -> 
    joinsig t tsk2 tls2' tls ->
    tsk1 = tsk2 /\ tls1' = tls2'.
Proof.
  introv Hjo1 Hjo2.
  assert (Hg1: get tls t = Some tsk1).
  { jeat. }
  assert (Hg2: get tls t = Some tsk2).
  { jeat. }
  assert (Heq: tsk1 = tsk2).
  {
    congruence.
  }
  split; auto.
  subst tsk1. rename tsk2 into tsk.
  unfolds in Hjo1. unfolds in Hjo2.
  eapply map_join_cancel; eauto.
Qed. 

Lemma set_set_swap:
  forall (tls: TcbMod.map) t1 t2 a1 a2,
    t1 <> t2 ->
    set (set tls t1 a1) t2 a2 = set (set tls t2 a2) t1 a1. 
Proof.
  introv Hneq.
  apply map_eql.
  intros.
  casetac t1 t He Hne.
  - subst.
    rewrite map_get_set.
    rewrite neq_set_get; eauto.
    rewrite map_get_set.
    auto.
  -
    casetac t2 t He_ Hne_.
    + subst.
      rewrite map_get_set.
      rewrite neq_set_get; eauto.
      rewrite map_get_set.
      auto.
    + repeat (rewrite neq_set_get; eauto).
Qed. 

Lemma q_set_set_swap:
  forall (qls: QueMod.map) (q1 q2: qid) a1 a2,
    q1 <> q2 ->
    set (set qls q1 a1) q2 a2 = set (set qls q2 a2) q1 a1. 
Proof.
  introv Hneq.
  apply map_eql.
  intro q.
  casetac q1 q He Hne.
  - subst.
    rewrite map_get_set.
    rewrite neq_set_get; eauto.
    rewrite map_get_set.
    auto.
  -
    casetac q2 q He_ Hne_.
    + subst.
      rewrite map_get_set.
      rewrite neq_set_get; eauto.
      rewrite map_get_set.
      auto.
    + repeat (rewrite neq_set_get; eauto).
Qed. 

Lemma qls_set_set_latter:
  forall (qls: QueMod.map) qid a b, 
    set (set qls qid a) qid b = set qls qid b.
Proof.
  intros.
  apply map_eql.
  intros.
  rename t into q.
  casetac qid q He Hne.
  - subst. repeat rewrite map_get_set.
    auto.
  - repeat rewrite neq_set_get; eauto.
Qed. 

Lemma beq_tid_eq:
  forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H; destruct t1; destruct t2.
  apply andb_true_iff in H; destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Pos.eqb_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.

Lemma beq_tid_neq :
  forall x y, x <> y -> beq_tid x y = false.
Proof.
  introv Hneq.
  destruct (beq_tid x y) eqn: E.
  apply beq_tid_eq in E.
  false.
  auto.
Qed. 

Lemma remove_tid_swap:
  forall t1 t2 ts,
    t1 <> t2 -> 
    remove_tid t1 (remove_tid t2 ts) = remove_tid t2 (remove_tid t1 ts).
Proof.
  intros t1 t2 ts Hneq.
  induction ts as [ |t ts IH].
  - simpl.
    reflexivity.
  - simpl.

    destruct (beq_tid t2 t) eqn:H2.
    + (* t2 = t *)
      assert (Ht : t2 = t).
      {
        apply beq_tid_eq.
        exact H2.
      }
      subst t.

      rewrite (beq_tid_neq t1 t2 Hneq).
      simpl.

      destruct (beq_tid t1 t2) eqn:H1.
      * exfalso.
        apply Hneq.
        apply beq_tid_eq.
        exact H1.
      * simpl.
        rewrite beq_tid_true.
        rewrite IH.
        reflexivity.

    + (* t2 <> t *)
      simpl.

      destruct (beq_tid t1 t) eqn:H1.
      * (* t1 = t *)
        assert (Ht : t1 = t).
        {
          apply beq_tid_eq.
          exact H1.
        }
        subst t.
        auto.

      * (* t1 <> t *)
        simpl.
        rewrite H2.
        rewrite IH.
        reflexivity.
Qed.                  

Lemma tickchange_swap:
  forall t st tls qls st' qls' t0 st0 tls' st'0 tls'0 qls'0 p p0 msg0 sus0 msg sus td td0, 
    t <> t0 -> 
    tickchange t st qls st' qls' -> 
    tickchange t0 st0 qls' st'0 qls'0 ->
    set tls t (p, st', msg, sus, td) = tls' ->
    set tls' t0 (p0, st'0, msg0, sus0, td0) = tls'0 ->
    (exists tls1 qls1,
        tickchange t0 st0 qls st'0 qls1 /\
          tickchange t st qls1 st' qls'0 /\
          set tls t0 (p0, st'0, msg0, sus0, td0) = tls1 /\
          set tls1 t (p, st', msg, sus, td) = tls'0). 
Proof.
  introv Hneqt Htch Htch0 Hset Hset0.
  inverts Htch; inverts Htch0; subst tls'; subst tls'0.
  -
    do 2 eexists.
    split. constructors; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. constructors; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. eapply wait_que_rdy; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. constructors; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. constructors; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. eapply wait_que_rdy; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. constructors; eauto.
    split. constructors; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    do 2 eexists.
    split. constructors; eauto.
    split. eapply wait_que_rdy; eauto.
    split; eauto.
    apply set_set_swap.
    apply not_eq_sym; auto.
  -
    casetac qid qid0 He Hne.
    + subst.
      rewrite map_get_set in H1.
      inverts H1.
      do 2 eexists.
      split. eapply wait_que_rdy; eauto.
      split. constructors; eauto.
      rewrite map_get_set. eauto.
      
      do 2 rewrite qls_set_set_latter.
      rewrite remove_tid_swap; eauto.
      split; eauto.
      apply set_set_swap.
      apply not_eq_sym; auto.
    +
      rewrite neq_set_get in H1; eauto.
      do 2 eexists.
      split. eapply wait_que_rdy; eauto.
      split. constructors; eauto.
      rewrite neq_set_get; eauto.
      apply q_set_set_swap; auto.
      split; eauto.
      apply set_set_swap.
      apply not_eq_sym; auto.
Qed.

Lemma tickstep'_ind:
  forall td tls qls tls'' qls'' tls0, 
    tickstep' td tls qls tls'' qls'' tls0 ->
    forall tls0_ p msg sus td' st t, 
      joinsig t (p, st, msg, sus, td') tls0_ tls0 ->
      ((td' = td /\ 
          exists st' tls' qls', 
            tickchange t st qls st' qls' /\ 
              tls' = set tls t (p, st', msg, sus, td) /\
              tickstep' td tls' qls' tls'' qls'' tls0_)
       \/
         td' <> td /\
           tickstep' td tls qls tls'' qls'' tls0_
      ). 
Proof.
  introv Hstep.
  induction Hstep.
  - introv Hemp.
    unfolds in Hemp.
    apply map_join_pos' in Hemp.
    inverts Hemp.
  -
    introv Hjo.
    casetac t t0 He Hne.
    + subst.
      lets H__: joinsig_eq H Hjo.
      destruct H__ as (Hteq & Htlseq).
      inverts Hteq.
      subst.
      left. split; auto.
      do 3 eexists; splits; eauto.
    + 
      assert (Hg0: get tls_used t0 = Some (p0, st0, msg, sus, td')).
      {
        jeat.
      }
      assert (Hg: get tls_used' t0 = Some (p0, st0, msg, sus, td')).
      {
        clear -Hne Hg0 H.
        unfolds in H.
        assert (get tls_used t0 = get tls_used' t0).
        { 
          eapply map_join_get_none; eauto.
          eapply get_sig_none; eauto.
        }
        congruence.
      }
      assert (Hex: exists tls'', join (sig t0 (p0, st0, msg, sus, td')) tls'' tls_used').
      { eapply get_join; eauto. }
      destruct Hex as (tls''_ & Hjo''_).
      lets H_: IHHstep Hjo''_.

      assert (Hjo_: join (sig t0 (p0, st0, msg, sus, td')) (merge tls''_ (sig t (p, st, msg0, sus0, td))) tls_used).
      {
        unfolds in H.
        clear -Hjo''_ H.
        apply join_comm in H.
        eapply join_join_merge23_join; eauto.
      }
      unfolds in Hjo.
      lets H__: joinsig_eq Hjo Hjo_.
      destruct H__ as (Heqtup & Htlseq).

      assert (Hjo'_: join (sig t (p, st, msg0, sus0, td)) tls''_ tls0_).
      {
        assert (Hdisj: disjoint (sig t (p, st, msg0, sus0, td)) tls_used').
        {
          eapply join_disj; eauto.
        }
        assert (Hdisj': disjoint (sig t (p, st, msg0, sus0, td)) tls''_).
        {
          eapply join_merge in Hjo''_; eauto.
          rewrite Hjo''_ in Hdisj.
          eapply disj_merge_elim_r in Hdisj; eauto.
          apply Hdisj.
        }
        apply join_comm.
        eapply disj_sym in Hdisj'; eauto.
        eapply join_sem; eauto.
      }
      assert (Hjosig: joinsig t (p, st, msg0, sus0, td) tls''_ tls0_).
      { unfolds. auto. }

      casetac td' td Hed Hned.
      2: {
        right.
        split; auto.
        destruct H_ as [Heq_ | Hneq_].
        simpljoin; tryfalse.
        destruct Hneq_ as (_ & Hstep').
        clear Heqtup.
        clear Htlseq.            
        lets H__: ext_step Hjo'_ H0 H1 Hstep'; auto.
      }

      (* td' = td *)
      subst td'.
      destruct H_ as [Heq | Hneq].
      2: { simpljoin; tryfalse. }
      destruct Heq as (_ & Hex).
      destruct Hex as (st'_ & tls'_ & qls'_ & Htch_ & Htls'_ & Hstep'_).
      lets H_: tickchange_swap Hne H0 Htch_ H1 (eq_sym Htls'_).
      destruct H_ as (tls1 & qls1 & Htc1_ & Htc2_ & Hsettls1 & Hsettls'_).
      left.
      split; auto.
      do 3 eexists.
      splits; eauto.
      clear Htlseq. 
      clear Heqtup.
      clear Hjo_.
      clear Htch_.
      rewrite Hsettls1.
      clear Hsettls1.
      lets H__: ext_step Hjosig Htc2_ Hsettls'_; eauto.
      
  -
    introv Hjosig.
    casetac t t0 He Hne. 
    + subst.
      lets H__: joinsig_eq H Hjosig.
      destruct H__ as (Hteq & Htlseq).
      inverts Hteq.
      subst.
      right. 
      split; auto.
    + 
      assert (Hg0: get tls_used t0 = Some (p0, st0, msg, sus, td'0)).
      {
        jeat.
      }
      assert (Hg: get tls_used' t0 = Some (p0, st0, msg, sus, td'0)).
      {
        clear -Hne Hg0 H.
        unfolds in H.
        assert (get tls_used t0 = get tls_used' t0).
        { 
          eapply map_join_get_none; eauto.
          eapply get_sig_none; eauto.
        }
        congruence.
      }
      assert (Hex: exists tls'', join (sig t0 (p0, st0, msg, sus, td'0)) tls'' tls_used').
      { eapply get_join; eauto. }
      destruct Hex as (tls''_ & Hjo''_).
      lets H_: IHHstep Hjo''_.

      assert (Hjo_: join (sig t0 (p0, st0, msg, sus, td'0)) (merge tls''_ (sig t (p, st, msg0, sus0, td'))) tls_used).
      {
        unfolds in H.
        clear -Hjo''_ H.
        apply join_comm in H.
        eapply join_join_merge23_join; eauto.
      }
      unfolds in Hjosig.
      lets H__: joinsig_eq Hjosig Hjo_.
      destruct H__ as (Heqtup & Htlseq).

      assert (Hjo'_: join (sig t (p, st, msg0, sus0, td')) tls''_ tls0_).
      {
        assert (Hdisj: disjoint (sig t (p, st, msg0, sus0, td')) tls_used').
        {
          eapply join_disj; eauto.
        }
        assert (Hdisj': disjoint (sig t (p, st, msg0, sus0, td')) tls''_).
        {
          eapply join_merge in Hjo''_; eauto.
          rewrite Hjo''_ in Hdisj.
          eapply disj_merge_elim_r in Hdisj; eauto.
          apply Hdisj.
        }
        apply join_comm.
        eapply disj_sym in Hdisj'; eauto.
        eapply join_sem; eauto.
      }
      assert (Hjosig_: joinsig t (p, st, msg0, sus0, td') tls''_ tls0_).
      { unfolds. auto. }

      destruct H_ as [Heq | Hneq].
      * destruct Heq as (Htdeq_ & Hex).
        destruct Hex as (st'_ & tls'0_ & qls'0_ & Htc_& Htls'0_ & Hts').
        left. 
        split; auto.
        do 3 eexists; splits; eauto.
        clear Heqtup.
        clear Htlseq.
        eapply ext_step_no_change; eauto.
      * destruct Hneq as (Hne_ & Hstep'_).
        right. split; auto.
        eapply ext_step_no_change; eauto.
Qed.

Lemma joinsig_ex_tsk_in_dom_impl:
  forall t t0 pr st m sus td tls1' tls2' tls1 tls2
         (Hjo1: join (sig t (pr, st, m, sus, td)) tls1' tls1)
         (Hjo2: join (sig t (pr, st, m, sus, td)) tls2' tls2)
         (Heqv0: ex_tsk_in_dom t0 td tls1 <-> ex_tsk_in_dom t0 td tls2)
         (Hex1: ex_tsk_in_dom t0 td tls1'),
    ex_tsk_in_dom t0 td tls2'. 
Proof.
  intros.
  unfold ex_tsk_in_dom. unfold ex_tsk_in_dom in Hex1.
  destruct Hex1 as (pr1 & st1 & m1 & sus1 & Hgt1).
  unfolds in Hjo1.
  casetac t0 t He Hne.
  * subst. 
    assert (Hnone: get tls1' t = None).
    {
      clear -Hjo1 Hgt1.
      eapply map_join_get_no_perm1; eauto.
      rewrite get_a_sig_a; eauto.
    }
    false.
  * 
    assert (Hg10: get tls1 t0 = Some (pr1, st1, m1, sus1, td)).
    {
      jeat.
    }
    assert (Hex20: ex_tsk_in_dom t0 td tls2).
    {
      eapply Heqv0; eauto.
      unfolds. do 4 eexists; eauto.
    }
    unfolds in Hex20.
    destruct Hex20 as (pr20 & st20 & m20 & sus20 & Hg20).
    assert (get tls2' t0 = Some (pr20, st20, m20, sus20, td)).
    {
      clear -Hjo2 Hne Hg20.
      assert (Hgeq20: get tls2 t0 = get tls2' t0).
      {
        eapply map_join_get_none; eauto.
        eapply get_a_sig_a'; eauto.
      }
      congruence.
    }
    do 4 eexists; eauto.
Qed.


Lemma joinsig_tls_equiv_inner: 
  forall t tls1' tls1 tls2 td p st msg sus, 
    joinsig t (p, st, msg, sus, td) tls1' tls1 ->
    tls_equiv td tls1 tls2 ->
    exists tls2', 
      joinsig t (p, st, msg, sus, td) tls2' tls2 /\
        tls_equiv td tls1' tls2'.
Proof. 
  introv Hjs Hte.
  unfolds in Hte.
  assert (Hte_ := Hte).
  specialize (Hte t).
  assert (Hg: get tls1 t = Some (p, st, msg, sus, td)).
  { jeat. } 
  assert (Hex: ex_tsk_in_dom t td tls1).
  {
    unfolds.
    do 4 eexists; eauto.
  }
  destruct Hte as (Heqv & Hteq).
  apply Heqv in Hex.
  unfolds in Hex.
  destruct Hex as (pr2 & st2 & m2 & sus2 & Hgt2).
  assert (Hex2: exists tls2', join (sig t (pr2, st2, m2, sus2, td)) tls2' tls2).
  {
    eapply get_join; eauto.
  }
  destruct Hex2 as (tls2' & Hjo2).
  lets H__: Hteq Hg Hgt2.
  specializes H__; eauto.
  simpljoin.
  unfold joinsig.
  eexists; split; eauto.
  { (* tls_equiv *) 
    unfolds.
    intros.
    specialize (Hte_ t0).
    destruct Hte_ as (Heqv0 & Htlseq0).
    split.
    -
      split; intros.
      +
        unfolds in Hjs. 
        lets H_: joinsig_ex_tsk_in_dom_impl Hjs Hjo2 Heqv0.
        eapply H_; eauto.
      +
        symmetry in Heqv0.
        eapply joinsig_ex_tsk_in_dom_impl; eauto.
    -
      introv Hg1' Hg2' Htd.
      eapply Htlseq0; eauto.
      jeat. jeat. 
  }
Qed. 

Lemma ex_mq_in_dom_set_prsv: 
  forall q td qls1 qls2 qid0 ts1 ts2 ms1 ms2 sz1 sz2 t, 
    (ex_mq_in_dom q td qls1 <-> ex_mq_in_dom q td qls2) ->
    (ex_mq_in_dom q td (set qls1 qid0 (msgq ms1 sz1 (remove_tid t ts1), td)) <->
       ex_mq_in_dom q td (set qls2 qid0 (msgq ms2 sz2 (remove_tid t ts2), td))). 
Proof.
  introv Hexeq.
  unfold ex_mq_in_dom in *.
  casetac qid0 q He Hne.
  - subst.
    repeat rewrite map_get_set.
    split; intro.
    + do 3 eexists; eauto.
    + do 3 eexists; eauto.
  - repeat rewrite neq_set_get; eauto.
Qed.

Lemma tickchange2_obsr_equiv_prsv_:
  forall O1 O2 qls1 qls2 t st1' st2' qls1' qls2' O1' O2' tls1 tls2 p st msg sus td, 
    I O1 -> I O2 -> 

    get O1 abstcblsid = Some (abstcblist tls1) -> 
    get O2 abstcblsid = Some (abstcblist tls2) ->
    get tls1 t = Some (p, st, msg, sus, td) -> 
    get tls2 t = Some (p, st, msg, sus, td) ->

    obsr_equiv_mqs td O1 O2 ->
    get O1 quelsid = Some (absecblist qls1) ->
    get O2 quelsid = Some (absecblist qls2) ->
    tickchange t st qls1 st1' qls1' -> 
    tickchange t st qls2 st2' qls2' -> 
    get O1' quelsid = Some (absecblist qls1') ->
    get O2' quelsid = Some (absecblist qls2') ->
    (st1' = st2' /\ obsr_equiv_mqs td O1' O2'). 
Proof.
  introv Hinv1 Hinv2 Hgtls1 Hgtls2 Hgt1 Hgt2 Hdteq12 Hqls1 Hqls2.
  introv Htc1 Htc2 Hqls1' Hqls2'.
  destruct Hdteq12 as (Heqv12 & Heq12).
  unfold obsr_equiv_mqs.
  inverts Htc1; inverts Htc2.
  - split; eauto.
    split.
    + 
      (* (exists qls, get O1' quelsid = ...) <-> (exists qls, get O2' quelsid = ...) *)     
      split; intro; eexists; eauto.
    +
      introv Hgq1' Hgq2'.
      rewrite Hqls1' in Hgq1'. symmetry in Hgq1'; inverts Hgq1'.
      rewrite Hqls2' in Hgq2'. symmetry in Hgq2'; inverts Hgq2'.
      specializes Heq12; eauto.
  - rn_or Hor.
    destruct Hor; tryfalse.
    rn_or Hor.
    destruct Hor; tryfalse.
    inverts H.
    destruct H1 as (Hneq10 & Hneq00).
    rewrite Int.eq_true in Hneq00. false. 
  - rn_or Hor.
    destruct Hor; tryfalse.
    rn_or Hor.
    destruct Hor; tryfalse.
  - rn_or Hor.
    destruct Hor; tryfalse.
    rn_or Hor.
    destruct Hor; tryfalse.
    inverts H.
    destruct H0 as (Hneq10 & Hneq00).
    rewrite Int.eq_true in Hneq00. false. 
  - inverts H.
    split; auto.
    split.
    + (* (exists qls, get O1' quelsid = ...) <-> (exists qls, get O2' quelsid = ...) *)     
      split; intro; eexists; eauto.
    + 
      introv Hgq1' Hgq2'.
      rewrite Hqls1' in Hgq1'. symmetry in Hgq1'; inverts Hgq1'.
      rewrite Hqls2' in Hgq2'. symmetry in Hgq2'; inverts Hgq2'.
      lets H__: Heq12 qls1' qls2' q Hqls1 Hqls2.
      destruct H__ as (Heqv & Hall).
      split; auto.
  - inverts H.
    destruct H0 as (Hneq11 & Hneq01).
    rewrite Int.eq_true in Hneq11. false.
  - rn_or Hor.
    destruct Hor; tryfalse.
    rn_or Hor.
    destruct Hor; tryfalse.
  - inverts H.
    destruct H1 as (Hneq11 & Hneq01).
    rewrite Int.eq_true in Hneq11. false.
  - split; auto.
    inverts H.

    lets H1_: Hinv1.(inv_wt_mq) Hgtls1 Hgt1 Hqls1; eauto.
    destruct H1_ as (ms1 & sz1 & ts1 & Hgetq1 & Hin1).
    
    lets H2_: Hinv2.(inv_wt_mq) Hgtls2 Hgt2 Hqls2; eauto.
    destruct H2_ as (ms2 & sz2 & ts2 & Hgetq2 & Hin2).

    rewrite Hgetq1 in H0; symmetry in H0; inverts H0.
    rewrite Hgetq2 in H1; symmetry in H1; inverts H1.
    
    split.
    + split; intro; eexists; eauto.
    + 
      introv Hgq1' Hgq2'.
      rewrite Hqls1' in Hgq1'. symmetry in Hgq1'; inverts Hgq1'.
      rewrite Hqls2' in Hgq2'. symmetry in Hgq2'; inverts Hgq2'.
      assert (Heq12_ := Heq12).
      specialize (Heq12 qls1 qls2 q Hqls1 Hqls2).
      destruct Heq12 as (Heqv12_ & Hq12).
          
      split.
      * eapply ex_mq_in_dom_set_prsv; eauto.
      * casetac qid0 q He Hne.
        ** subst. repeat rewrite map_get_set.
           introv Heq1 Heq2 Hd.
           inverts Heq1. inverts Heq2.
           lets H__: Hq12 Hgetq1 Hgetq2.
           specializes H__; eauto.
           inverts H__.
           auto.
        ** repeat rewrite neq_set_get; eauto.
Qed. 

Lemma dte_tasks_set_t_2_prsv:
  forall td O1 O2 tls1 tls2 t p st msg sus tls1' tls2' st' O1' O2'
         (Hdte_t : obsr_equiv_tasks td O1 O2)
         (Hinv1 : I O1)
         (Hinv2 : I O2)
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt1 : get tls1 t = Some (p, st, msg, sus, td))
         (Hgt2 : get tls2 t = Some (p, st, msg, sus, td))
         (Htls1' : tls1' = set tls1 t (p, st', msg, sus, td))
         (Htls2' : tls2' = set tls2 t (p, st', msg, sus, td))
         (Hgtls1' : get O1' abstcblsid = Some (abstcblist tls1'))
         (Hgtls2' : get O2' abstcblsid = Some (abstcblist tls2')), 
    obsr_equiv_tasks td O1' O2'.
Proof.
  intros.
  unfold obsr_equiv_tasks in *.
  destruct Hdte_t as (Heqv & Hteq).
  split.
  - split; intros; eexists; eauto.
  - introv Hgtls1'_ Hgtls2'_.
    rewrite Hgtls1' in Hgtls1'_; symmetry in Hgtls1'_; inverts Hgtls1'_.
    rewrite Hgtls2' in Hgtls2'_; symmetry in Hgtls2'_; inverts Hgtls2'_.
    subst tls1'.
    subst tls2'.
    specialize (Hteq tls1 tls2 t0 Hgtls1 Hgtls2).
    destruct Hteq as (Hexeq & Htskeq).
    split.
    + unfold ex_tsk_in_dom.
      casetac t t0 He Hne.
      * subst. repeat rewrite map_get_set.
        split; intros; do 4 eexists; eauto.
      * repeat rewrite neq_set_get; eauto.
    + casetac t t0 He Hne.
      * subst. repeat rewrite map_get_set.
        introv Heq1 Heq2.
        symmetry in Heq1; inverts Heq1.
        symmetry in Heq2; inverts Heq2.
        intros. splits; eauto.
      * repeat rewrite neq_set_get; eauto.
Qed.
  
Lemma tickchange2_obsr_equiv_prsv:
  forall O1 O2 tls1 tls2 qls1 qls2 p st msg sus td t tls1' tls2' st1' st2' qls1' qls2' O1' O2', 
    obsr_equiv_tasks td O1 O2 ->
    obsr_equiv_mqs td O1 O2 ->
    I O1 -> I O2 -> 
    get O1 abstcblsid = Some (abstcblist tls1) -> 
    get O2 abstcblsid = Some (abstcblist tls2) ->
    get tls1 t = Some (p, st, msg, sus, td) -> 
    get tls2 t = Some (p, st, msg, sus, td) ->
    get O1 quelsid = Some (absecblist qls1) ->
    get O2 quelsid = Some (absecblist qls2) ->
    tickchange t st qls1 st1' qls1' -> 
    tickchange t st qls2 st2' qls2' -> 
    tls1' = set tls1 t (p, st1', msg, sus, td) ->
    tls2' = set tls2 t (p, st2', msg, sus, td) ->
    get O1' abstcblsid = Some (abstcblist tls1') ->
    get O2' abstcblsid = Some (abstcblist tls2') -> 
    get O1' quelsid = Some (absecblist qls1') ->
    get O2' quelsid = Some (absecblist qls2') ->
    obsr_equiv_tasks td O1' O2' /\ obsr_equiv_mqs td O1' O2'.
Proof.
  introv Hdte_t Hdte_q Hinv1 Hinv2 Hgtls1 Hgtls2 Hgt1 Hgt2.
  introv Hgqls1 Hgqls2 Htc1 Htc2 Htls1' Htls2' Hgtls1' Hgtls2' Hgqls1' Hgqls2'.
  lets H__: tickchange2_obsr_equiv_prsv_ Hinv1 Hinv2 Hgtls1 Hgtls2 Hgt1 Hgt2; eauto.
  specializes H__; eauto.
  destruct H__ as (Hst'eq & Hdte_q').
  subst st1'. rename st2' into st'.
  split; auto.
  clear Hgqls1 Hgqls2 Hgqls1' Hgqls2' Htc1 Htc2 Hdte_q Hdte_q'.
  lets H_: dte_tasks_set_t_2_prsv Hinv1 Hinv2 Hgtls1 Hgtls2; eauto.
Qed. 

Lemma tls_equiv_joinsig1_prsv:
  forall t td td' tls1 tls2 tls1' p st msg sus, 
    tls_equiv td tls1 tls2 ->
    joinsig t (p, st, msg, sus, td') tls1' tls1 -> 
    td' <> td -> 
    tls_equiv td tls1' tls2. 
Proof.
  introv Hte Hjo Hneq.
  unfold tls_equiv in *.
  intros.
  unfolds in Hjo.
  specialize (Hte t0).
  destruct Hte as (Heqv & Hteq).
  - split.
    unfolds.
    split.
    + introv Hex1'.
      destruct Hex1' as (pr1 & st1 & m1 & sus1 & Hgt1').
      eapply Heqv; eauto.
      assert (Hgt1: get tls1 t0 = Some (pr1, st1, m1, sus1, td)).
      { jeat. } 
      unfolds. do 4 eexists; eauto.
    + introv Hex.
      eapply Heqv in Hex.
      unfold ex_tsk_in_dom.
      unfold ex_tsk_in_dom in Hex.
      destruct Hex as (pr & st_ & m & sus_ & Hg).
      casetac t t0 He Hne.
      * subst.
        assert (Hgt: get tls1 t0 = Some (p, st, msg, sus, td')).
        { jeat. }
        rewrite Hgt in Hg; inverts Hg.
        false.
      *
        assert (Hgeq: get tls1 t0 = get tls1' t0).
        {
          eapply map_join_get_none; eauto.
          jeat.
        }
        rewrite <- Hgeq.
        do 4 eexists; eauto.
    +
      introv Hg1' Hg2'.
      eapply Hteq; eauto.
      jeat. 
Qed.
    
Lemma tickstep'2_dteq_preserved:
  forall td tls1 qls1 tls1' qls1' tls01, 
    tickstep' td tls1 qls1 tls1' qls1' tls01 ->
    forall tls2 qls2 tls2' qls2' tls02, 
    tickstep' td tls2 qls2 tls2' qls2' tls02 ->
    forall O1 O2 O1' O2'
           (Hinv1 : I O1)
           (Hinv2 : I O2)
           (Hsub1: Maps.sub tls01 tls1)
           (Hsub2: Maps.sub tls02 tls2)
           (Htlse: tls_equiv td tls01 tls02) 
           (Hdte_t : obsr_equiv_tasks td O1 O2)
           (Hdte_q : obsr_equiv_mqs td O1 O2)
           (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
           (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
           (Hgqls1 : get O1 quelsid = Some (absecblist qls1))
           (Hgqls2 : get O2 quelsid = Some (absecblist qls2))
           (Htls1' : get O1' abstcblsid = Some (abstcblist tls1'))
           (Htls2' : get O2' abstcblsid = Some (abstcblist tls2'))
           (Hqls1' : get O1' quelsid = Some (absecblist qls1'))
           (Hqls2' : get O2' quelsid = Some (absecblist qls2')),
      obsr_equiv_tasks td O1' O2' /\ obsr_equiv_mqs td O1' O2'.
Proof.
  introv Hstep1; 
  induction Hstep1; introv Hstep2; intros.
  - 
    assert (Heq: tls2 = tls2' /\ qls2 = qls2').
    {
      lets H__: not_ex_t_indom_tickstep'_nochange Hstep2; eauto.
      lets H_: tls_equiv_emp Htlse; eauto.
    }
    rename tls into tls1. rename qls into qls1.
    destruct Heq; subst.
    rename tls2' into tls2. rename qls2' into qls2.
    assert (H1'1: obsr_equiv_tasks td O1' O1).
    {
      eapply obsr_equiv_tasks_nochange; eauto.
      congruence.
    }
    assert (H22': obsr_equiv_tasks td O2 O2').
    {
      eapply obsr_equiv_tasks_nochange; eauto.
      congruence.
    }
    assert (H1'1_: obsr_equiv_mqs td O1' O1).
    {
      eapply obsr_equiv_mqs_nochange; eauto.
      congruence.
    }
    assert (H22'_: obsr_equiv_mqs td O2 O2').
    {
      eapply obsr_equiv_mqs_nochange.
      congruence.
    }
    split.
    + eapply dteq_tasks_trans with (O1:=O1') (O2:=O2) (O3:=O2'); eauto.
      eapply dteq_tasks_trans; eauto.
    + eapply dteq_mqs_trans with (O1:=O1') (O2:=O2) (O3:=O2'); eauto.
      eapply dteq_mqs_trans; eauto.
  -
    lets H__: joinsig_tls_equiv_inner H Htlse.
    destruct H__ as (tls2_used' & Hjo2 & Htlse').
    lets H_: tickstep'_ind Hstep2 Hjo2.
    destruct H_ as [Htdeq | Htdne]; [idtac | simpljoin; tryfalse].
    destruct Htdeq as (_ & Hex).    
    destruct Hex as (st'_ & tls2'_ & qls2'_ & Htc2 & Htls2'_ & Hstep2_).

    assert (Hgtu1: get tls_used t = Some (p, st, msg0, sus0, td)).
    { jeat. }
    assert (Hgtu2: get tls02 t = Some (p, st, msg0, sus0, td)).
    { jeat. } 
    assert (Hgt1: get tls t = Some (p, st, msg0, sus0, td)).
    { clear -Hsub1 Hgtu1. unfolds in Hsub1. simpljoin. jeat. }
    assert (Hgt2: get tls2 t = Some (p, st, msg0, sus0, td)).
    { clear -Hsub2 Hgtu2. unfolds in Hsub2. simpljoin. jeat. }

    set (O1'_ := set (set O1 abstcblsid (abstcblist tls')) quelsid (absecblist qls')).
    set (O2'_ := set (set O2 abstcblsid (abstcblist tls2'_)) quelsid (absecblist qls2'_)).
    
    assert (Hgt1': get O1'_ abstcblsid = Some (abstcblist tls')).
    {
      subst O1'_.
      rewrite neq_set_get; eauto.
      2: introv Hf; inverts Hf.
      rewrite map_get_set.
      auto.
    }
    assert (Hgt2': get O2'_ abstcblsid = Some (abstcblist tls2'_)).
    {
      subst O2'_.
      rewrite neq_set_get; eauto.
      2: introv Hf; inverts Hf.
      rewrite map_get_set.
      auto.
    }
    assert (Hgq1': get O1'_ quelsid = Some (absecblist qls')).
    {
      subst O1'_.
      rewrite map_get_set.
      auto.
    }      
    assert (Hgq2': get O2'_ quelsid = Some (absecblist qls2'_)).
    { 
      subst O2'_.
      rewrite map_get_set.
      auto.
    }

    assert (Hdteq': obsr_equiv_tasks td O1'_ O2'_ /\ obsr_equiv_mqs td O1'_ O2'_).
    {
      lets H__: tickchange2_obsr_equiv_prsv Hdte_t Hdte_q Hinv1 Hinv2 Hgtls1 Hgtls2; eauto.
    }
    
    destruct Hdteq' as (Hdteq_t' & Hdteq_q').
    assert (Hsub1_: Maps.sub tls_used' tls').
    {
      lets H_: sub_join_set_sub Hsub1; eauto.
    }
    assert (Hsub2_: Maps.sub tls2_used' tls2'_).
    {
      lets H_: sub_join_set_sub Hsub2 Hjo2; eauto.
    }
    assert (Hinv1_: I O1'_).
    {
      subst O1'_.
      lets H_: tickchange_prsv_inv Hinv1 Hgtls1 Hgt1; eauto.
    }
    assert (Hinv2_: I O2'_).
    {
      subst O2'_.
      lets H_: tickchange_prsv_inv Hinv2 Hgtls2 Hgt2; eauto.
    }
      
    lets IHHstep1_: IHHstep1 Hstep2_ Hinv1_ Hinv2_ Hsub1_ Hsub2_.
    instantiate (1:= O2') in IHHstep1_.
    instantiate (2:= O1') in IHHstep1_.
    specialize (IHHstep1_ Htlse' Hdteq_t' Hdteq_q').
    eapply IHHstep1_; eauto.

  -
    lets Htlse': tls_equiv_joinsig1_prsv Htlse H H0; eauto.
    assert (Hsub1_: Maps.sub tls_used' tls).
    {
      eapply sub_trans with (m2:=tls_used); eauto.
      unfolds.
      unfolds in H.
      eapply join_comm in H; eauto.
    }
    lets IHHstep1_: IHHstep1 Hstep2 Hinv1 Hinv2 Hsub1_ Hsub2 Htlse'.
    specialize (IHHstep1_ Hdte_t Hdte_q).
    eapply IHHstep1_; eauto.
Qed. 

Lemma dteq_tls_equiv:
  forall td O1 O2 tls1 tls2, 
    obsr_equiv_tasks td O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) -> 
    tls_equiv td tls1 tls2. 
Proof.
  introv Hdte Hg1 Hg2.
  unfold obsr_equiv_tasks in Hdte.
  unfolds.
  destruct Hdte as (_ & HH).
  intros.
  eapply HH; eauto.
Qed. 

Lemma tickstep2_dteq_preserved:
  forall td cd O1 O2 tls1 tls2 qls1 qls2 tls1' tls2' qls1' qls2' O1' O2', 
    I O1 -> I O2 -> 
    obsr_equiv_tasks td O1 O2 -> 
    obsr_equiv_mqs td O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) ->
    get O1 quelsid = Some (absecblist qls1) ->
    get O2 quelsid = Some (absecblist qls2) -> 
    tickstep cd tls1 qls1 tls1' qls1' ->
    tickstep cd tls2 qls2 tls2' qls2' ->
    get O1' abstcblsid = Some (abstcblist tls1') ->
    get O2' abstcblsid = Some (abstcblist tls2') ->
    get O1' quelsid = Some (absecblist qls1') ->
    get O2' quelsid = Some (absecblist qls2') -> 
    (obsr_equiv_tasks td O1' O2' /\ obsr_equiv_mqs td O1' O2').
Proof.
  introv Hinv1 Hinv2 Hdte_t Hdte_q Hgtls1 Hgtls2 Hgqls1 Hgqls2.
  introv Hstep1 Hstep2 Htls1' Htls2' Hqls1' Hqls2'.
  unfolds in Hstep1.
  unfolds in Hstep2.
  casetac cd td He Hne.
  -
    subst. 

    assert (Maps.sub tls1 tls1) by apply sub_refl.
    assert (Maps.sub tls2 tls2) by apply sub_refl.
    lets H__: tickstep'2_dteq_preserved Hstep1 Hstep2 Hinv1 Hinv2; eauto.
    specializes H__; eauto.
    eapply dteq_tls_equiv; eauto.
             
  -
    assert (H11': obsr_equiv_tasks td O1 O1' /\ obsr_equiv_mqs td O1 O1').
    { 
      lets H_: tickstep1_dteq_preserved Hstep1 Hinv1 Hgtls1; eauto.
      apply sub_refl.
    }
    assert (H22': obsr_equiv_tasks td O2 O2' /\ obsr_equiv_mqs td O2 O2').
    {
      lets H_: tickstep1_dteq_preserved Hstep2 Hinv2 Hgtls2; eauto.
      apply sub_refl.
    }
    destruct H11' as (Ht11' & Hq11').
    destruct H22' as (Ht22' & Hq22').
    assert (Ht1'2: obsr_equiv_tasks td O1' O2).
    { 
      clear -Ht11' Hdte_t.
      apply dteq_tasks_sym in Ht11'.
      eapply dteq_tasks_trans; eauto.
    }
    assert (Hq1'2: obsr_equiv_mqs td O1' O2).
    {
      clear -Hq11' Hdte_q.
      apply dteq_mqs_sym in Hq11'.
      eapply dteq_mqs_trans; eauto.
    }
    split.
    + clear -Ht1'2 Ht22'.
      eapply dteq_tasks_trans; eauto.
    + clear -Hq1'2 Hq22'.
      eapply dteq_mqs_trans; eauto.
Qed. 

Lemma tck_dte_holds:
  forall O1 O2 t1 t2 vl1' vl2' O1' O2' td cid
         (Htck1 : has_tick' tickisr t1 cid O1 vl1' O1')
         (Htck2 : has_tick' tickisr t2 cid O2 vl2' O2')
         (Hinv1 : I O1)
         (Hinv2 : I O2)
         (Hoesch : obsr_equiv_data SchedDom O1 O2)
         (Hoed : obsr_equiv_data (TaskDom td) O1 O2), 
    obsr_equiv_tskd td O1' O2' /\ vl1' = vl2'. 
Proof.
  intros.
  unfold tickisr, has_tick' in *.
  destruct Htck1; destruct Htck2; simpljoin; tryfalse.
  2: destruct H0; simpljoin; tryfalse.
  2: destruct H; simpljoin; tryfalse.
  2: destruct H; simpljoin; tryfalse. 
  
  unfold tickisr_spec in *.
  
  destruct H as (tls1 & qls1 & ctid1 & dtmp1 & dt1 & cdmp1 & cd1 & cid1 & Hgct1 &
                   Hgt1 & Hgtls1 & Hgqls1 & Hgdtmp1 & Hgdt1 & Hact1 & Hgcmp1 & Hgcd1 & Hex1).
  
  destruct H0 as (tls2 & qls2 & ctid2 & dtmp2 & dt2 & cdmp2 & cd2 & cid2 & Hgct2 &
                    Hgt2 & Hgtls2 & Hgqls2 & Hgdtmp2 & Hgdt2 & Hact2 & Hgcmp2 & Hgcd2 & Hex2). 

  destruct Hex1 as (tls1' & qls1' & Hstep1 & Hif1).
  destruct Hex2 as (tls2' & qls2' & Hstep2 & Hif2).
  inverts Hoesch.
  assert (Hcideq: cid1 = cid2).
  { congruence. }
  rename cid2 into cid0.
  assert (dt1 = dt2).
  {
    congruence.
  }
  subst.
  rename dt2 into dt.

  d_if_hyp.

  - (* case where current domain changes *) 
    destruct Hif1 as (imp1 & lmp1 & ldmp1 & scdmp1 & idx1 & len1 & ld1 & schd1 & H1').
    destruct Hif2 as (imp2 & lmp2 & ldmp2 & scdmp2 & idx2 & len2 & ld2 & schd2 & H2').
    destruct H1' as (Hgimp1 & Hgidx1 & Hglmp1 & Hglen1 & (* Hgcmp1 & Hgcd1 & *) Hgldmp1 &
                       Hgld1 & Hgscdmp1 & Hgschd1 & H1').
    destruct H2' as (Hgimp2 & Hgidx2 & Hglmp2 & Hglen2 & (* Hgcmp2 & Hgcd2 & *) Hgldmp2 &
                       Hgld2 & Hgscdmp2 & Hgschd2 & H2').
    assert (schd1 = schd2).
    { congruence. } 
    subst schd1. rename schd2 into schd.
    assert (len1 = len2).
    { congruence. }
    subst len1. rename len2 into len.
    assert (idx1 = idx2).
    { congruence. }
    subst idx1. rename idx2 into idx.
    assert (cd1 = cd2).
    { congruence. }
    subst cd1. rename cd2 into cd.

    d_mt_hyp.
    + destruct p.
      simpl in Hoed.
      destruct H1'. destruct H2'.
      split; try congruence.
      inverts Hoed.
      
      lets H__: tickstep2_dteq_preserved Hinv1 Hinv2 oe_td_tasks oe_td_mqs Hgtls1 Hgtls2. 
      lets H_: H__ Hgqls1 Hgqls2 Hstep1 Hstep2. clear H__.

      assert (Hconj: obsr_equiv_tasks td O1' O2' /\ obsr_equiv_mqs td O1' O2').
      {
        subst O1'. subst O2'.
        eapply H_; eauto. clear H_.
        do 5 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail)).
        rewrite map_get_set; auto.
        do 5 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail)).
        rewrite map_get_set; auto.
        do 4 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail)).
        rewrite map_get_set; auto.          
        do 4 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail)).
        rewrite map_get_set; auto.          
      }
      clear H_.
      
      constructors.
      *
        apply Hconj.
      *
        apply Hconj. 
      * 
        assert (H1'1: obsr_equiv_chans td O1' O1).
        {
          eapply obsr_equiv_chs_nochange; eauto.
          subst O1'.
          repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
        }        
        assert (H22': obsr_equiv_chans td O2 O2').
        { 
          eapply obsr_equiv_chs_nochange; eauto.
          subst O2'.
          repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
        }          
        assert (H1'2: obsr_equiv_chans td O1' O2).
        {
          lets H_: dteq_chs_trans H1'1 oe_td_chs; eauto.
        }
        eapply dteq_chs_trans; eauto.
      * 
        assert (H1'1: obsr_equiv_freetids td O1' O1).
        {
          eapply obsr_equiv_fts_nochange; eauto.
          subst O1'.
          repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
        }        
        assert (H22': obsr_equiv_freetids td O2 O2').
        { 
          eapply obsr_equiv_fts_nochange; eauto.
          subst O2'.
          repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
        }          
        assert (H1'2: obsr_equiv_freetids td O1' O2).
        {
          lets H_: dteq_fts_trans H1'1 oe_td_fts; eauto.
        }
        eapply dteq_fts_trans; eauto.
      *
        assert (H1'1: obsr_equiv_freeqids td O1' O1).
        {
          eapply obsr_equiv_fqs_nochange; eauto.
          subst O1'.
          repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
        }        
        assert (H22': obsr_equiv_freeqids td O2 O2').
        { 
          eapply obsr_equiv_fqs_nochange; eauto.
          subst O2'.
          repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
        }          
        assert (H1'2: obsr_equiv_freeqids td O1' O2).
        {
          lets H_: dteq_fqs_trans H1'1 oe_td_fqs; eauto.
        }
        eapply dteq_fqs_trans; eauto.

    + simpljoin. split; auto.

  - (* case where curent domain does not change *)   
    assert (cid = cid0) by congruence.
    subst cid0.
    simpl in Hoed.
    destruct Hif1. destruct Hif2.
    split; try congruence.
    inverts Hoed. 
      
    assert (cd1 = cd2).
    { congruence. }
    subst cd1. rename cd2 into cd.

    lets H__: tickstep2_dteq_preserved Hinv1 Hinv2 oe_td_tasks oe_td_mqs Hgtls1 Hgtls2. 
    lets H_: H__ Hgqls1 Hgqls2 Hstep1 Hstep2. clear H__.
    instantiate (1:=O2') in H_. instantiate (1:=O1') in H_.
    
    assert (Hconj: obsr_equiv_tasks td O1' O2' /\ obsr_equiv_mqs td O1' O2').
    {
      subst O1'. subst O2'.
      eapply H_; eauto. clear H_.
      - 
        do 2 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail)).
        rewrite map_get_set; auto.
      -
        do 2 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail)).
        rewrite map_get_set; auto.
      -
        rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail).
        rewrite map_get_set; auto.
      -
        rewrite neq_set_get; eauto; try (introv Hf; inverts Hf; fail). 
        rewrite map_get_set; auto.          
    }
    clear H_.
    constructors.
    *
      apply Hconj.
    *
      apply Hconj. 
    * 
      assert (H1'1: obsr_equiv_chans td O1' O1).
      {
        eapply obsr_equiv_chs_nochange; eauto.
        subst O1'.
        repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
      }        
      assert (H22': obsr_equiv_chans td O2 O2').
      { 
        eapply obsr_equiv_chs_nochange; eauto.
        subst O2'.
        repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
      }          
      assert (H1'2: obsr_equiv_chans td O1' O2).
      {
        lets H_: dteq_chs_trans H1'1 oe_td_chs; eauto.
      }
      eapply dteq_chs_trans; eauto.
    * 
      assert (H1'1: obsr_equiv_freetids td O1' O1).
      {
        eapply obsr_equiv_fts_nochange; eauto.
        subst O1'.
        repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
      }        
      assert (H22': obsr_equiv_freetids td O2 O2').
      { 
        eapply obsr_equiv_fts_nochange; eauto.
        subst O2'.
        repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
      }          
      assert (H1'2: obsr_equiv_freetids td O1' O2).
      {
        lets H_: dteq_fts_trans H1'1 oe_td_fts; eauto.
      }
      eapply dteq_fts_trans; eauto.
    *
      assert (H1'1: obsr_equiv_freeqids td O1' O1).
      {
        eapply obsr_equiv_fqs_nochange; eauto.
        subst O1'.
        repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
      }        
      assert (H22': obsr_equiv_freeqids td O2 O2').
      { 
        eapply obsr_equiv_fqs_nochange; eauto.
        subst O2'.
        repeat (rewrite neq_set_get; eauto; try (introv Hf; tryfalse; fail)).
      }          
      assert (H1'2: obsr_equiv_freeqids td O1' O2).
      {
        lets H_: dteq_fqs_trans H1'1 oe_td_fqs; eauto.
      }
      eapply dteq_fqs_trans; eauto.
    
Qed. 

Lemma tck_dte_sch_holds:
  forall O1 O2 t1 t2 cid vl1' vl2' O1' O2'
    (Hinv1 : I O1)
    (Hinv2 : I O2)
    (Hoesch: obsr_equiv_data SchedDom O1 O2)
    (Htck1 : has_tick' tickisr t1 cid O1 vl1' O1')
    (Htck2 : has_tick' tickisr t2 cid O2 vl2' O2'), 
    obsr_equiv_data SchedDom O1' O2' /\ vl1' = vl2'. 
      
Proof. 
  intros.
  unfold tickisr, has_tick' in *.
  destruct Htck1; destruct Htck2; simpljoin; tryfalse.
  2: { destruct H0; simpljoin; tryfalse. }
  2: { destruct H; simpljoin; tryfalse. }
  2: { destruct H; simpljoin; tryfalse. } 

  unfold tickisr_spec in *.
  
  destruct H as (tls1 & qls1 & ctid1 & dtmp1 & dt1 & cdmp1 & cd1 & cid1 & Hgct1 &
                   Hgt1 & Hgtls1 & Hgqls1 & Hgdtmp1 & Hgdt1 & Hact1 & Hgcmp1 & Hgcd1 & Hex1).
  
  destruct H0 as (tls2 & qls2 & ctid2 & dtmp2 & dt2 & cdmp2 & cd2 & cid2 & Hgct2 &
                    Hgt2 & Hgtls2 & Hgqls2 & Hgdtmp2 & Hgdt2 & Hact2 & Hgcmp2 & Hgcd2 & Hex2). 

  destruct Hex1 as (tls1' & qls1' & Hstep1 & Hif1).
  destruct Hex2 as (tls2' & qls2' & Hstep2 & Hif2).
  inverts Hoesch.
  assert (Hcideq: cid1 = cid2).
  { congruence. }
  rename cid2 into cid0.
  assert (dt1 = dt2).
  {
    congruence.
  }
  subst.
  rename dt2 into dt.

  d_if_hyp.

  - (* case where current domain changes *)  
    destruct Hif1 as (imp1 & lmp1 & ldmp1 & scdmp1 & idx1 & len1 & ld1 & schd1 & H1').
    destruct Hif2 as (imp2 & lmp2 & ldmp2 & scdmp2 & idx2 & len2 & ld2 & schd2 & H2').
    destruct H1' as (Hgimp1 & Hgidx1 & Hglmp1 & Hglen1 & (* Hgcmp1 & Hgcd1 & *) Hgldmp1 &
                       Hgld1 & Hgscdmp1 & Hgschd1 & H1').
    destruct H2' as (Hgimp2 & Hgidx2 & Hglmp2 & Hglen2 & (* Hgcmp2 & Hgcd2 & *) Hgldmp2 &
                       Hgld2 & Hgscdmp2 & Hgschd2 & H2').
    assert (schd1 = schd2).
    { congruence. } 
    subst schd1. rename schd2 into schd.
    assert (len1 = len2).
    { congruence. }
    subst len1. rename len2 into len.
    assert (idx1 = idx2).
    { congruence. }
    subst idx1. rename idx2 into idx.
    assert (cd1 = cd2).
    { congruence. }
    subst cd1. rename cd2 into cd.

    d_mt_hyp.
    + destruct p.
      destruct H1'. destruct H2'.
      split; try congruence.
      constructors; subst O1'; subst O2'.
      * 
        rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
        rewrite map_get_set. 
        rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
        rewrite map_get_set. 
        assert (cdmp1 = cdmp2) by congruence.
        congruence.
      * 
        repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
      *        
        do 3 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        do 3 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        assert (imp1 = imp2) by congruence.
        congruence.
      *
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      *
        rewrite map_get_set.
        rewrite map_get_set.
        assert (dtmp1 = dtmp2) by congruence.
        congruence. 
    +
      simpljoin.
      split; auto.
      unfolds. 
      constructors; try congruence.

  - (* case where current domain does not change *)  
    destruct Hif1; destruct Hif2.
    split; try congruence.
    constructors; subst O1'; subst O2'.
    * 
      repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    *
      repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    *
      repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    *
      repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    *
      rewrite map_get_set.
      rewrite map_get_set.
      assert (dtmp1 = dtmp2) by congruence.
      congruence.
Qed. 
    

Lemma tck_oe_sch_cdomeq:
  forall O1 O2 t1 t2 cid vl1' vl2' O1' O2'
         (Hinv1 : I O1)
         (Hinv2 : I O2)
         (Hoesch : obsr_equiv_data SchedDom O1 O2)
         (Htck1 : has_tick' tickisr t1 cid O1 vl1' O1')
         (Htck2 : has_tick' tickisr t2 cid O2 vl2' O2')
         (td : task_dom), 
    cur_dom O1' cid td <-> cur_dom O2' cid td. 
Proof.
  intros.
  unfold tickisr, has_tick' in *.
  destruct Htck1; destruct Htck2; simpljoin; tryfalse.
  2: { destruct H0; simpljoin; tryfalse. }
  2: { destruct H; simpljoin; tryfalse. }
  2: { destruct H0; simpljoin; tryfalse. }

  unfold tickisr_spec in *.
  
  destruct H as (tls1 & qls1 & ctid1 & dtmp1 & dt1 & cdmp1 & cd1 & cid1 & Hgct1 &
                   Hgt1 & Hgtls1 & Hgqls1 & Hgdtmp1 & Hgdt1 & Hact1 & Hgcmp1 & Hgcd1 & Hex1).
  
  destruct H0 as (tls2 & qls2 & ctid2 & dtmp2 & dt2 & cdmp2 & cd2 & cid2 & Hgct2 &
                    Hgt2 & Hgtls2 & Hgqls2 & Hgdtmp2 & Hgdt2 & Hact2 & Hgcmp2 & Hgcd2 & Hex2). 

  destruct Hex1 as (tls1' & qls1' & Hstep1 & Hif1).
  destruct Hex2 as (tls2' & qls2' & Hstep2 & Hif2).
  inverts Hoesch.
  assert (Hcideq: cid1 = cid2).
  { congruence. }
  rename cid2 into cid0.
  assert (dt1 = dt2).
  { congruence. }
  subst.
  rename dt2 into dt.

  d_if_hyp.

  - (* case where current domain changes *)
    destruct Hif1 as (imp1 & lmp1 & ldmp1 & scdmp1 & idx1 & len1 & ld1 & schd1 & H1').
    destruct Hif2 as (imp2 & lmp2 & ldmp2 & scdmp2 & idx2 & len2 & ld2 & schd2 & H2').
    destruct H1' as (Hgimp1 & Hgidx1 & Hglmp1 & Hglen1 & (* Hgcmp1 & Hgcd1 & *) Hgldmp1 &
                       Hgld1 & Hgscdmp1 & Hgschd1 & H1').
    destruct H2' as (Hgimp2 & Hgidx2 & Hglmp2 & Hglen2 & (* Hgcmp2 & Hgcd2 & *) Hgldmp2 &
                       Hgld2 & Hgscdmp2 & Hgschd2 & H2').
    assert (schd1 = schd2).
    { congruence. } 
    subst schd1. rename schd2 into schd.
    assert (len1 = len2).
    { congruence. }
    subst len1. rename len2 into len.
    assert (idx1 = idx2).
    { congruence. }
    subst idx1. rename idx2 into idx.
    assert (cd1 = cd2).
    { congruence. }
    subst cd1. rename cd2 into cd.

    d_mt_hyp.
    + 
      destruct p. 
      destruct H1' as (HO1' & Hvl1').
      destruct H2' as (HO2' & Hvl2').
      subst O1'; subst O2'.
      unfold cur_dom.
      unfold state.
      unfold get_cur_dom.
      rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
      rewrite map_get_set.
      rewrite neq_set_get; eauto; try (introv Hf; inverts Hf). 
      rewrite map_get_set.
      assert (cdmp1 = cdmp2) by congruence.
      subst. tauto.
    +
      destruct H1' as (HO1' & Hvl1').
      destruct H2' as (HO2' & Hvl2').
      subst O1'; subst O2'.
      unfold cur_dom.
      unfold state.
      unfold get_cur_dom.
      assert (cdmp1 = cdmp2) by congruence.
      subst.
      rewrite oe_sch_cd_eq.
      tauto.
      
  - (* case where current domain does not change *)
    destruct Hif1 as (HO1' & Hvl1').
    destruct Hif2 as (HO2' & Hvl2').
    subst O1'; subst O2'. 
    unfold cur_dom.
    unfold state.
    unfold get_cur_dom.
    repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    rewrite oe_sch_cd_eq.
    tauto.
Qed. 
