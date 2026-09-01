
Require Import LibTactics.
Require Import join_lib.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import rules. 

Require Import specs_common.
Require Import state.
Require Import my_tacs.

Require Import task_apispecs. 
Require Import sys_spec.

Require Import rly_guar.
Require Import flow_policy.
Require Import obsr_equiv. 

Require Import aux_lemmas.
Require Import inv_props.
Require Import dteq_props.

Definition tdel_release_post (vl: vallist) (t: tid) (vl': vallist) (O: osabst) := 
    (exists i, vl' = Vint32 i :: nil).  

Lemma tdel_release_post_sat:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Htdel : task_del_tcb_release t vl O ac (vl', O')), 
    tdel_release_post vl t vl' O'. 
Proof.
  intros.
  unfolds.
  unfolds in Htdel.
  d_mt_hyp.
  - inv_errp.
  - d_mt_hyp; try (inv_errp; tryfalse).
    d_mt_hyp; try (inv_errp; tryfalse; try eexists; eauto; fail).
    do 2 (d_if_hyp; try (inv_errp; tryfalse; try eexists; eauto; fail)).
    destruct Htdel as (tls & prc & stc & msgc & susc & dc & Hgtls & Hgt & Hor).
    destruct Hor as [Herr | Hok]. 
    + simpljoin; inv_errp.
      eexists; eauto.
    + destruct Hok as (t' & st & msg & su & Hgt' & Hor).
      destruct Hor as [Herr | Hok].
      * simpljoin; inv_errp.
        eexists; eauto.
      * destruct Hok as (Hrdy & fts & tids & Hgftmp & Hgfts & Hex & tls').
        simpljoin; subst.
        unfold cont.
        eexists; eauto.
Qed.



Lemma joinsig_tls_ex_tsk_in_dom:
  forall t pr st msg su dc tls' tls i0 t0,  
    joinsig t (pr, st, msg, su, dc) tls' tls -> 
    dc <> i0 -> 
    (ex_tsk_in_dom t0 i0 tls <-> ex_tsk_in_dom t0 i0 tls'). 
Proof.
  introv Hjos Hned.
  unfold ex_tsk_in_dom.
  split; introv Hex.
  - destruct Hex as (pr_ & st_ & m & sus & Hgt0).
    assert (Hgt: get tls t = Some (pr, st, msg, su, dc)).
    {
      jeat.
    }
    casetac t0 t He Hne.
    + subst.
      rewrite Hgt0 in Hgt. inverts Hgt. false.
    + unfolds in Hjos.
      assert (Hgteq: get tls t0 = get tls' t0).
      {
        eapply map_join_get_none; eauto.
        jeat. 
      }
      rewrite <- Hgteq.
      do 4 eexists; eauto.
  -
    destruct Hex as (pr_ & st_ & m & sus & Hgt0).
    casetac t t0 He Hne.
    + subst.
      unfolds in Hjos.
      assert (Hgs: get (sig t0 (pr, st, msg, su, dc)) t0 = Some (pr, st, msg, su, dc)).
      {
        jeat.
      }
      jeat.
    +
      do 4 eexists; jeat. 
Qed. 

Lemma tdel_obsr_equiv_tasks:
  forall t O tls prc stc msgc susc dc i0 t' pr msg su ftmp ts tls' 
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (prc, stc, msgc, susc, dc))
         (Hgt' : get tls t' = Some (pr, rdy, msg, su, dc))
         (Hgftmp : get O freetid = Some (freetidlist ftmp))
         (Hgts : get ftmp dc = Some ts)
         (Hjos : joinsig t' (pr, rdy, msg, su, dc) tls' tls)
         (Hsd : sdom O t dc)
         (Hneqd : dc <> i0), 
    obsr_equiv_tasks i0 O
      (set (set O abstcblsid (abstcblist tls')) freetid
         (freetidlist (set ftmp dc (ts ++ t' :: nil)))). 
Proof.
  intros.
  splits.
  - rew_neq.
    rewrite map_get_set.
    split.
    + intros. eexists; eauto.
    + introv Hex.
      destruct Hex as (tls_ & Heq).
      inverts Heq.
      eexists; eauto.
  -
    introv Hg1 Hg2.
    rew_neq_in Hg2.
    rewrite map_get_set in Hg2.
    inverts Hg2.
    uni_12_sym (get O abstcblsid).
    split.
    +
      eapply joinsig_tls_ex_tsk_in_dom; eauto.
    +
      introv Hg1 Hg2 Hd.
      subst d1.
      casetac t0 t' He Hne.
      * subst.
        unfolds in Hjos.
        assert (Hgs: get (sig t' (pr, rdy, msg, su, dc)) t' = Some (pr, rdy, msg, su, dc)).
        {
          jeat.
        }
        clear -Hjos Hgs Hg2.
        false. 
        eapply map_join_get_some with (x:=sig t' (pr, rdy, msg, su, dc)); eauto.
      *
        assert (Hgteq: get tls t0 = get tls2 t0).
        {
          clear -Hjos Hne.
          unfolds in Hjos.
          eapply map_join_get_none; eauto.
          jeat. 
        }
        rewrite Hg1 in Hgteq.
        rewrite Hg2 in Hgteq.
        inverts Hgteq.
        splits; eauto.
Qed. 

Lemma tdel_obsr_equiv_fts:
  forall t O tls pr msg su dc t' ftmp ts tls' i0
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt' : get tls t' = Some (pr, rdy, msg, su, dc))
         (Hgftmp : get O freetid = Some (freetidlist ftmp))
         (Hgts : get ftmp dc = Some ts)
         (Hjos : joinsig t' (pr, rdy, msg, su, dc) tls' tls)
         (Hneqd : dc <> i0), 
    obsr_equiv_freetids i0 O
      (set (set O abstcblsid (abstcblist tls')) freetid
         (freetidlist (set ftmp dc (ts ++ t' :: nil)))). 
Proof.
  intros.
  unfolds.
  rewrite map_get_set.
  split.
  - split.
    + 
      intros; eexists; eauto.
    +
      introv Hex.
      destruct Hex as (fts & Heq).
      inverts Heq.
      eexists; eauto.
  -
    introv Hg1 Hg2.
    inverts Hg2.
    rew_neq.
    rewrite Hgftmp in Hg1.
    inverts Hg1.
    tauto.
Qed. 

Lemma tdel_obsr_equiv_tskd:
  forall O tls tls' t prc stc msgc susc dc i0 t' pr msg su ftmp ts 
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (prc, stc, msgc, susc, dc))
         (Hgt' : get tls t' = Some (pr, rdy, msg, su, dc))
         (Hgftmp : get O freetid = Some (freetidlist ftmp))
         (Hgts : get ftmp dc = Some ts)
         (Hjos : joinsig t' (pr, rdy, msg, su, dc) tls' tls)
         (Hsd : sdom O t dc)
         (Hneqd : dc <> i0), 
    obsr_equiv_tskd i0 O
      (set (set O abstcblsid (abstcblist tls')) freetid
         (freetidlist (set ftmp dc (ts ++ t' :: nil)))).
Proof.
  intros.
  constructors.
  -
    eapply tdel_obsr_equiv_tasks; eauto.
  -
    eapply obsr_equiv_mqs_nochange; eauto.
    repeat rew_neq.
  -
    eapply obsr_equiv_chs_nochange; eauto.
    repeat rew_neq.    
  -
    eapply tdel_obsr_equiv_fts; eauto.
  -
    eapply obsr_equiv_fqs_nochange; eauto.
    repeat rew_neq.    
Qed. 

Lemma tdel_obsr_equiv_data:
  forall vl t O ac vl' O' td d 
         (Htvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Htdel : task_del_tcb_release t vl O ac (vl', O'))
         (Hnex : ~ (exists cid, ac = _TickAct cid))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d), 
    obsr_equiv_data d O O'. 
Proof.
  intros.
  unfolds in Htdel.
  do 3 (d_mt_hyp; try inv_errp).
  d_if_hyp; try inv_errp; try (apply obsr_equiv_data_refl; fail).
  2: {
    simpl in H.
    subst.
    simpl.
    apply obsr_equiv_data_refl.
  }

  d_if_hyp; try (inv_errp; apply obsr_equiv_data_refl; fail).
  destruct Htdel as (tls & prc & stc & msgc & susc & dc & Hgtls & Hgt & Hor).
  destruct Hor as [Herr | Hok]. 
  + simpljoin; inv_errp.
    apply obsr_equiv_data_refl.
  + destruct Hok as (t' & st & msg & su & Hgt' & Hor).
    destruct Hor as [Herr | Hok].
    * simpljoin. inv_errp. apply obsr_equiv_data_refl.
    * destruct Hok as (Hrdy & ftmp & ts & Hgftmp & Hgts & Hex).
      destruct Hex as (tls' & Hjos & HO' & Hac & Hvl').
      subst.
      clear Hnex.
      destruct d.
      ** simpl.
         assert (Hneqd: td <> i0).
         {
           casetac td i0 He Hne.
           - subst.
             false. apply Hnfl. constructors.
           - auto.
         }
         assert (dc = td).
         {
           eapply tls_sdom_td_eq with (t:=t); eauto.
           apply Hpre1.
         }
         subst td.
         eapply tdel_obsr_equiv_tskd; eauto.
      **
        simpl.
        constructors; repeat rew_neq.
Qed. 

Lemma tdel2_obsr_equiv_tasks_prsv: 
  forall td td' O1 O2 t tls1 tls2 t' pr msg su fts1 tids1 fts2 tids2 tls1' tls2'
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hsd1 : sdom O1 t td')
         (Hsd2 : sdom O2 t td')
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1' : get tls1 t' = Some (pr, rdy, msg, su, td'))
         (Hgfts1 : get O1 freetid = Some (freetidlist fts1))
         (Hgtids1 : get fts1 td' = Some tids1)
         (Hjos1 : joinsig t' (pr, rdy, msg, su, td') tls1' tls1)
         (* (Hgt1 : get tls1 t = Some (prc1, stc1, msgc1, susc1, td')) *)
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2' : get tls2 t' = Some (pr, rdy, msg, su, td'))
         (Hgfts2 : get O2 freetid = Some (freetidlist fts2))
         (Hgtids2 : get fts2 td' = Some tids2)
         (Hjos2 : joinsig t' (pr, rdy, msg, su, td') tls2' tls2)
  (* (Hgt2 : get tls2 t = Some (prc2, stc2, msgc2, susc2, td')) *), 

    obsr_equiv_tasks td
      (set (set O1 abstcblsid (abstcblist tls1')) freetid
         (freetidlist (set fts1 td' (tids1 ++ t' :: nil))))
      (set (set O2 abstcblsid (abstcblist tls2')) freetid
         (freetidlist (set fts2 td' (tids2 ++ t' :: nil)))).
  
Proof.
  intros.
  unfolds.
  rew_neq. rewrite map_get_set.
  rew_neq. rewrite map_get_set.
  split.
  - split; intros; eexists; eauto.
  - introv Hg1 Hg2.
    symmetry in Hg1. inverts Hg1.
    symmetry in Hg2. inverts Hg2.
    assert (Hexeqv: ex_tsk_in_dom t0 td tls1 <-> ex_tsk_in_dom t0 td tls2).
    {
      eapply Hdte; auto.
    }
    split.
    +
      unfold ex_tsk_in_dom in *.
      unfolds in Hjos1.
      unfolds in Hjos2.
      casetac t' t0 He Hne.
      * subst.
        assert (Hn1: get tls1' t0 = None).
        {
          jeat.
        }
        assert (Hn2: get tls2' t0 = None).
        {
          jeat.
        }
        rewrite Hn1. rewrite Hn2.
        tauto.
      *
        assert (Heq1: get tls1 t0 = get tls1' t0).
        {
          eapply map_join_get_none; eauto.
          jeat.
        }
        assert (Heq2: get tls2 t0 = get tls2' t0).
        {
          eapply map_join_get_none; eauto.
          jeat.
        }
        rewrite <- Heq1.
        rewrite <- Heq2.
        auto.
    +
      introv Hg1 Hg2 Hd.
      subst d1.
      casetac t' t0 He Hne.
      * subst.
        assert (Hn1: get tls1' t0 = None).
        {
          jeat.
        }
        rewrite Hg1 in Hn1. false.
      *
        assert (Heq1: get tls1 t0 = get tls1' t0).
        {
          eapply map_join_get_none; eauto.
          jeat.
        }
        assert (Heq2: get tls2 t0 = get tls2' t0).
        {
          eapply map_join_get_none; eauto.
          jeat.
        }
        rewrite <- Heq1 in Hg1.
        rewrite <- Heq2 in Hg2.
        eapply Hdte; eauto.
Qed.         
  
Lemma tdel2_obsr_equiv_fts_prsv:
  forall td O1 O2 fts1 fts2 td' tids1 tids2 t' tls1' tls2'
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (* Hsd1 : sdom O1 t td' *)
         (* Hsd2 : sdom O2 t td' *)
         (Hgfts1 : get O1 freetid = Some (freetidlist fts1))
         (Hgtids1 : get fts1 td' = Some tids1)
         (Hgfts2 : get O2 freetid = Some (freetidlist fts2))
         (Hgtids2 : get fts2 td' = Some tids2), 

    obsr_equiv_freetids td
      (set (set O1 abstcblsid (abstcblist tls1')) freetid
         (freetidlist (set fts1 td' (tids1 ++ t' :: nil))))
      (set (set O2 abstcblsid (abstcblist tls2')) freetid
         (freetidlist (set fts2 td' (tids2 ++ t' :: nil)))). 
Proof.
  intros.
  unfolds. rewrite map_get_set. rewrite map_get_set.
  split.
  - split; 
      intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    inverts Hg1.
    inverts Hg2.
    simpl in Hdte'.
    inverts Hdte'.
    unfolds in oe_td_fts.
    destruct oe_td_fts as (Heqv & Hall).
    lets H__: Hall Hgfts1 Hgfts2.
    eapply H__ in Hgtids1; eauto.
    Set Printing Implicit.
    unfold freetids.B in Hgtids1.
    rewrite Hgtids2 in Hgtids1.
    inverts Hgtids1.
    Unset Printing Implicit.
    rename tids1 into tids.
    casetac td' td He Hne.
    + subst.
      do 2 rewrite map_get_set.
      tauto.
    + do 2 rew_neq.
      simpl in Hdte.
      eapply Hdte; eauto.
Qed.       

Lemma tdel2_obsr_equiv_tskd_prsv: 
  forall td td' O1 O2 t tls1 tls2 t' pr msg su fts1 tids1 fts2 tids2 tls1' tls2'
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hsd1 : sdom O1 t td')
         (Hsd2 : sdom O2 t td')
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1' : get tls1 t' = Some (pr, rdy, msg, su, td'))
         (Hgfts1 : get O1 freetid = Some (freetidlist fts1))
         (Hgtids1 : get fts1 td' = Some tids1)
         (Hjos1 : joinsig t' (pr, rdy, msg, su, td') tls1' tls1)
         (* (Hgt1 : get tls1 t = Some (prc1, stc1, msgc1, susc1, td')) *)
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2' : get tls2 t' = Some (pr, rdy, msg, su, td'))
         (Hgfts2 : get O2 freetid = Some (freetidlist fts2))
         (Hgtids2 : get fts2 td' = Some tids2)
         (Hjos2 : joinsig t' (pr, rdy, msg, su, td') tls2' tls2)
  (* (Hgt2 : get tls2 t = Some (prc2, stc2, msgc2, susc2, td')) *), 

    obsr_equiv_tskd td
      (set (set O1 abstcblsid (abstcblist tls1')) freetid
         (freetidlist (set fts1 td' (tids1 ++ t' :: nil))))
      (set (set O2 abstcblsid (abstcblist tls2')) freetid
         (freetidlist (set fts2 td' (tids2 ++ t' :: nil)))). 

Proof.
  intros.
  constructors.
  -
    eapply tdel2_obsr_equiv_tasks_prsv; eauto.
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
    eapply tdel2_obsr_equiv_fts_prsv; eauto. 
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

Lemma tdel2_obsr_equiv_data_prsv:
  forall t O1 O2 vl ac1 ac2 vl1' vl2' O1' O2' td
         (Htvm : tl_vl_match (Tint8 :: nil) vl = true) 
         (Hpre2 : pre2 t O1 O2 trivial_asrt td obsr_equiv_data flows_to)
         (Hdel1 : task_del_tcb_release t vl O1 ac1 (vl1', O1'))
         (Hdel2 : task_del_tcb_release t vl O2 ac2 (vl2', O2'))
         (Hnex1 : ~ (exists cid, ac1 = _TickAct cid))
         (Hnex2 : ~ (exists cid, ac2 = _TickAct cid)), 
    obsr_equiv_data (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'.
Proof.
  intros.
  simpl.
  des_pre2 Hpre2.
  unfolds in Hdel1.
  unfolds in Hdel2.
  do 2 (d_mt_hyp; try inv_errp).
  d_mt_hyp.
  -
    d_if_hyp.
    + inv_errp; inv_errp.
      splits; eauto.
    +
      d_if_hyp.
      *
        inv_errp; inv_errp.
        splits; eauto.
      *
        destruct Hdel1 as (tls1 & prc1 & stc1 & msgc1 & susc1 & dc1 & Hgtls1 & Hgt1 & Hor1).
        destruct Hdel2 as (tls2 & prc2 & stc2 & msgc2 & susc2 & dc2 & Hgtls2 & Hgt2 & Hor2).
        assert (dc1 = td').
        {
          lets H_: tls_sdom_td_eq Hpre11; eauto.
        }
        subst dc1. 
        assert (dc2 = td').
        {
          lets H_: tls_sdom_td_eq Hpre12; eauto.
        }
        subst dc2.
        rename i into pr.

        (* pose proof (ex_tsk_or tls1 td' pr) as Hexor1. *)
        lets Heqv: ex_prio_eqv pr Hdte' Hgtls1 Hgtls2.
        clear Hnex1 Hnex2.
        destruct Hor1 as [(Hnex1 & Herr1) | Hex1].
        **
          rewrite Heqv in Hnex1.
          destruct Hor2 as [(Hnex2 & Herr2) | Hex2].
          *** 
            subst. inv_errp; inv_errp; tryfalse. 
            splits; auto.
          ***
            false.
            apply Hnex1.
            simpljoin.
            false. apply Hnex1. do 4 eexists; eauto.
        **
          destruct Hor2 as [(Hnex2 & Herr2) | Hex2].
          ***
            rewrite <- Heqv in Hnex2.
            simpljoin; false; apply Hnex2; do 4 eexists; eauto.
          ***
            destruct Hex1 as (t1' & st1 & msg1 & su1 & Hgt1' & Hor1).
            destruct Hex2 as (t2' & st2 & msg2 & su2 & Hgt2' & Hor2).
            assert (Heqt: t1' = t2').
            {
              lets Hexeqv: dte_ex_tsk_in_dom_same t1' Hdte' Hgtls1 Hgtls2.
              assert (Hex2: exists pr0 st m sus0, get tls2 t1' = Some (pr0, st, m, sus0, td')).
              {
                eapply Hexeqv; eauto.
              }
              destruct Hex2 as (pr2_ & st2_ & m2_ & su2_ & Hgt1'2).
              lets Heqs: obsr_equiv_data_tsk_eq Hdte' Hgtls1 Hgtls2 Hgt1' Hgt1'2.
              destructs Heqs; subst.
              destruct Hpre12 as (Hp2 & Hinv2).
              inverts Hinv2.
              unfolds in inv_tsk_diff_idpr.
              casetac t1' t2' He Hne; auto.

              lets H__: inv_tsk_diff_idpr Hgtls2 Hne Hgt1'2 Hgt2'.
              false.
            }
            subst t1'. rename t2' into t'.

            lets Heqs: obsr_equiv_data_tsk_eq Hdte' Hgtls1 Hgtls2 Hgt1' Hgt2'.
            destructs Heqs; subst.
            rename st2 into st.
            rename msg2 into msg.
            rename su2 into su. 
            destruct st.
            ****
              destruct Hor1 as [Hwt1 | Hrdy1].
              {
                destruct Hwt1 as (Heq1 & Herr1).
                simpljoin; tryfalse.
              }
              destruct Hor2 as [Hwt2 | Hrdy2].
              {
                destruct Hwt2 as (Heq2 & Herr2).
                simpljoin; tryfalse.
              }
              destruct Hrdy1 as (_ & Hex1).
              destruct Hrdy2 as (_ & Hex2).
              destruct Hex1 as (fts1 & tids1 & Hgfts1 & Hgtids1 & Hex1).
              destruct Hex2 as (fts2 & tids2 & Hgfts2 & Hgtids2 & Hex2).
              destruct Hex1 as (tls1' & Hjos1 & HO1' & Hac1 & Hvl1').
              destruct Hex2 as (tls2' & Hjos2 & HO2' & Hac2 & Hvl2').
              subst.
              splits; eauto.

              eapply tdel2_obsr_equiv_tskd_prsv; eauto.

            ****
              destruct Hor1 as [Hwt1 | Hrdy1];
                destruct Hor2 as [Hwt2 | Hrdy2];
                simpljoin; tryfalse. 
              {
                inv_errp.
                inv_errp.
                splits; eauto.
              }              
        
  -
    inv_errp; inv_errp.
    simpl in *.
    subst.
    splits; auto.
    
Qed. 

(*new_add*)

Lemma taskdel_tcb_release_prsv_inv:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Htdel : task_del_tcb_release t vl O ac (vl', O')),
    I O'.
Proof.
  intros.
  destruct Hpre1 as (Htriv & Hinv).
  unfold task_del_tcb_release in Htdel.
  do 3 (d_mt_hyp; try (inv_errp; exact Hinv)).
  d_if_hyp; try (inv_errp; exact Hinv).
  d_if_hyp; try (inv_errp; exact Hinv).
  destruct Htdel as
      (tls & prc & stc & msgc & susc & dc & Hgtls & Hgt & Hor).
  destruct Hor as [Herr | Hok].
  - simpljoin. inv_errp. exact Hinv.
  - destruct Hok as (tdel & st & msg & su & Hgtdel & Hor).
    destruct Hor as [Herr | Hok].
    + simpljoin. inv_errp. exact Hinv.
    + destruct Hok as
          (Hrdy & fts & tids & Hgfts & Hgtids & tls' & Hjoin &
           HO' & Hac & Hvl').
      subst O'. change (I_ O) in Hinv. destruct Hinv as
          [Haf Hdom Hprio Hqaf Hqdom Hmqwt Hwtmq Hchs].
      subst st.
      constructors.
      * unfold tsk_active_free_disj in *.
        intros t0 td Ha Hf.
        unfold ex_active_tsk in Ha. unfold ex_free_tsk in Hf.
        destruct Ha as (tls0 & pr0 & st0 & msg0 & sus0 & Htls0 & Hget0).
        destruct Hf as (fts0 & tids0 & Hfts0 & Hgettids0 & Hin).
        rew_neq_in Htls0. rewrite map_get_set in Htls0.
        injection Htls0 as Heqtls0. subst tls0.
        rewrite map_get_set in Hfts0.
        injection Hfts0 as Heqfts0. subst fts0.
        casetac dc td He Hne.
        -- subst td. rewrite map_get_set in Hgettids0. inverts Hgettids0.
           apply in_app_or in Hin. destruct Hin as [Hin | Hin].
           ++ eapply Haf with (t:=t0) (td:=dc).
              ** unfold ex_active_tsk. do 5 eexists; split; eauto.
                 assert (Hneqdel : t0 <> tdel).
                 { introv Heq. subst t0. unfold joinsig in Hjoin.
                   eapply map_join_get_some with
                       (x:=sig tdel (i, rdy, msg, su, dc)); eauto. jeat. }
                 assert (Hgeq : get tls t0 = get tls' t0).
                 { unfold joinsig in Hjoin.
                   eapply map_join_get_none; eauto. jeat. }
                 rewrite Hgeq; exact Hget0.
              ** unfold ex_free_tsk. do 2 eexists; splits; eauto.
           ++ simpl in Hin. destruct Hin as [Heq | Hfalse]; tryfalse.
              subst t0. unfold joinsig in Hjoin.
              eapply map_join_get_some with
                  (x:=sig tdel (i, rdy, msg, su, dc)); eauto. jeat.
        -- rewrite neq_set_get in Hgettids0; auto.
           eapply Haf with (t:=t0) (td:=td).
           ++ unfold ex_active_tsk. do 5 eexists; split; eauto.
              assert (Hneqdel : t0 <> tdel).
              { introv Heq. subst t0. unfold joinsig in Hjoin.
                eapply map_join_get_some with
                    (x:=sig tdel (i, rdy, msg, su, dc)); eauto. jeat. }
              assert (Hgeq : get tls t0 = get tls' t0).
              { unfold joinsig in Hjoin.
                eapply map_join_get_none; eauto. jeat. }
              rewrite Hgeq; exact Hget0.
           ++ unfold ex_free_tsk. do 2 eexists; splits; eauto.
      * unfold tsk_dom_disj in *.
        intros t0 td1 td2 Hsd1 Hsd2.
        assert (Hback : forall td, sdom_ (set (set O abstcblsid
          (abstcblist tls')) freetid
          (freetidlist (set fts dc (tids ++ tdel :: nil)))) t0 td ->
          sdom_ O t0 td).
        { intros td Hsd. destruct Hsd as [Ha | Hf].
          - left. unfold ex_active_tsk in *.
            destruct Ha as (tls0 & pr & st0 & msg0 & sus & Htls0 & Hg0).
            rew_neq_in Htls0. rewrite map_get_set in Htls0. inverts Htls0.
            do 5 eexists; split; eauto. unfold joinsig in Hjoin; jeat.
          - unfold ex_free_tsk in *.
            destruct Hf as (fts0 & ts0 & Hfts0 & Hg0 & Hin).
            rewrite map_get_set in Hfts0. inverts Hfts0.
            casetac dc td He Hne.
            + subst td. rewrite map_get_set in Hg0. inverts Hg0.
              apply in_app_or in Hin. destruct Hin as [Hin | Hin].
              * right. do 2 eexists; splits; eauto.
              * simpl in Hin. destruct Hin as [Heq | Hfalse]; tryfalse.
                subst t0. left. do 5 eexists; split; eauto.
            + rewrite neq_set_get in Hg0; auto.
              right. do 2 eexists; splits; eauto. }
        eapply Hdom; eauto.
      * unfold tsk_diff_id_prio in *.
        intros tls0 Htls0 t1 t2 td pr1 st1 msg1 sus1 pr2 st2 msg2 sus2
               Hneq Hg1 Hg2.
        rew_neq_in Htls0. rewrite map_get_set in Htls0. inverts Htls0.
        eapply Hprio with (tls:=tls) (t1:=t1) (t2:=t2) (td:=td); eauto;
          unfold joinsig in Hjoin; jeat.
      * eapply same_mqs_que_active_free_disj with (O:=O); eauto;
          repeat rew_neq.
      * eapply same_mqs_que_dom_disj with (O:=O); eauto;
          repeat rew_neq.
      * unfold mq_wt_cond in *.
        intros qls q ms sz ts td tls0 t0 Hqls Htls0 Hgq Hin.
        rew_neq_in Hqls. rew_neq_in Htls0.
        rewrite map_get_set in Htls0.
        injection Htls0 as Heqtls0. subst tls0.
        specialize (Hmqwt qls q ms sz ts td tls t0).
        rew_neq_in Hqls.
        specialize (Hmqwt Hqls Hgtls Hgq Hin).
        destruct Hmqwt as (pr & msg0 & sus & to & Hwait).
        assert (Hneqdel : t0 <> tdel).
        { introv Heq. subst t0.
          pose proof (eq_trans (eq_sym Hwait) Hgtdel) as Hsame.
          inverts Hsame. }
        do 4 eexists.
        assert (Hgeq : get tls t0 = get tls' t0).
        { unfold joinsig in Hjoin.
          eapply map_join_get_none; eauto. jeat. }
        rewrite <- Hgeq. exact Hwait.
      * unfold wt_mq_cond in *.
        intros qls tls0 t0 pr q to msg0 sus td Htls0 Hwait Hqls.
        rew_neq_in Htls0. rewrite map_get_set in Htls0.
        injection Htls0 as Heqtls0. subst tls0.
        assert (Hwaitold : get tls t0 =
          Some (pr, wait (os_stat_qpend q) to, msg0, sus, td)).
        { unfold joinsig in Hjoin; jeat. }
        specialize (Hwtmq qls tls t0 pr q to msg0 sus td Hgtls Hwaitold).
        repeat rew_neq_in Hqls.
      * eapply same_chs_chs_sat_config with (O:=O); eauto.
        repeat rew_neq.
Qed.
Lemma taskdel_tcb_release_guar:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Htdel : task_del_tcb_release t vl O ac (vl', O')),
    guar_tsk_env t O O'.
Proof.
  intros.
  unfold task_del_tcb_release in Htdel.
  do 3 (d_mt_hyp; try (inv_errp; apply guar_tsk_refl)).
  d_if_hyp; try (inv_errp; apply guar_tsk_refl).
  d_if_hyp; try (inv_errp; apply guar_tsk_refl).
  destruct Htdel as
      (tls & prc & stc & msgc & susc & dc & Hgtls & Hgt & Hor).
  destruct Hor as [Herr | Hok].
  - simpljoin. inv_errp. apply guar_tsk_refl.
  - destruct Hok as (t' & st & msg & su & Hgt' & Hor).
    destruct Hor as [Herr | Hok].
    + simpljoin. inv_errp. apply guar_tsk_refl.
    + destruct Hok as
          (Hrdy & fts & tids & Hgfts & Hgtids & tls' & Hjoin &
           HO' & Hac & Hvl').
      subst O'.
      unfold guar_tsk_env. split.
      * intros t0 td Hneq Hsd. unfold sdom_ in *.
        destruct Hsd as [Ha | Hf].
        -- unfold ex_active_tsk in *.
           destruct Ha as
               (tls0 & pr0 & st0 & msg0 & sus0 & Hgtls0 & Hget0).
           rewrite Hgtls in Hgtls0.
           injection Hgtls0 as Heq_tls. subst tls0.
           casetac t0 t' He Hne.
           ++ rewrite He in Hget0.
              pose proof (eq_trans (eq_sym Hget0) Hgt') as Hsame.
              inverts Hsame. subst t0.
              right. unfold ex_free_tsk.
              exists (set fts dc (tids ++ t' :: nil)).
              exists (tids ++ t' :: nil). splits.
              ** rewrite map_get_set. reflexivity.
              ** rewrite map_get_set. reflexivity.
              ** apply in_or_app. right. simpl; auto.
           ++ left. unfold ex_active_tsk.
              do 5 eexists. split.
              ** rew_neq. rewrite map_get_set. reflexivity.
              ** assert (Hgteq : get tls t0 = get tls' t0).
                 { unfold joinsig in Hjoin.
                   eapply map_join_get_none; eauto. jeat. }
                 rewrite <- Hgteq. exact Hget0.
        -- right. unfold ex_free_tsk in *.
           destruct Hf as (fts0 & tids0 & Hgfts0 & Hgtids0 & Hin).
           rewrite Hgfts in Hgfts0. inverts Hgfts0.
           exists (set fts0 dc (tids ++ t' :: nil)).
           casetac dc td He Hne.
           ++ subst td. rewrite Hgtids in Hgtids0. inverts Hgtids0.
              exists (tids0 ++ t' :: nil). splits.
              ** rewrite map_get_set. reflexivity.
              ** rewrite map_get_set. reflexivity.
              ** apply in_or_app. left; auto.
           ++ exists tids0. splits.
              ** rewrite map_get_set. reflexivity.
              ** rewrite neq_set_get; auto.
              ** auto.
      * introv Hqsd. unfold q_sdom_ in *.
        destruct Hqsd as [Ha | Hf].
        -- left. unfold ex_active_que in *.
           repeat rew_neq.
        -- right. unfold ex_free_que in *.
           repeat rew_neq.
Qed.

Lemma taskdel_tcb_release_sdom_iff:
  forall vl t O ac vl' O'
         (Htvm : tl_vl_match (Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Htdel : task_del_tcb_release t vl O ac (vl', O')),
    forall t0 td, sdom O t0 td <-> sdom O' t0 td.
Proof.
  intros vl t O ac vl' O' Htvm Hpre1 Htdel.
  assert (Hguar : guar_tsk_env t O O').
  { eapply taskdel_tcb_release_guar; eauto. }
  assert (Hinv : I O) by (apply Hpre1).
  unfold task_del_tcb_release in Htdel.
  do 3 (d_mt_hyp; try (inv_errp; reflexivity)).
  d_if_hyp.
  { inv_errp; tauto. }
  d_if_hyp.
  { inv_errp; tauto. }
  destruct Htdel as
      (tls & prc & stc & msgc & susc & dc & Hgtls & Hgt & Hor).
  destruct Hor as [Herr | Hok].
  - simpljoin. inv_errp; tauto.
  - destruct Hok as (tdel & st & msg & su & Hgtdel & Hor).
    destruct Hor as [Herr | Hok].
    + simpljoin. inv_errp; tauto.
    + destruct Hok as
          (Hrdy & fts & tids & Hgfts & Hgtids & tls' & Hjoin &
           HO' & Hac & Hvl').
      subst O'. intros tx domx. split.
      * intro Hsd.
        casetac t tx He Hne.
        -- subst tx.
           assert (Hsddc : sdom_ O t dc).
           { left. unfold ex_active_tsk. do 5 eexists; eauto. }
           assert (domx = dc).
           { change (I_ O) in Hinv.
             eapply Hinv.(inv_tsk_d_disj); eauto. }
           subst domx. casetac t tdel Het Hnet.
           ++ subst tdel. right. unfold ex_free_tsk.
              exists (set fts dc (tids ++ t :: nil)).
              exists (tids ++ t :: nil). splits.
              ** rewrite map_get_set. reflexivity.
              ** rewrite map_get_set. reflexivity.
              ** apply in_or_app. right. simpl; auto.
           ++ left. unfold ex_active_tsk.
              do 5 eexists. split.
              ** rew_neq. rewrite map_get_set. reflexivity.
              ** assert (Hgeq : get tls t = get tls' t).
                 { unfold joinsig in Hjoin.
                   eapply map_join_get_none; eauto. jeat. }
                 rewrite <- Hgeq. exact Hgt.
        -- unfold guar_tsk_env in Hguar.
           eapply Hguar; eauto.
      * intro Hsd. unfold sdom_ in Hsd |- *.
        destruct Hsd as [Ha | Hf].
        -- left. unfold ex_active_tsk in *.
           destruct Ha as
               (tls0 & pr0 & st0 & msg0 & sus0 & Htls0 & Hget0).
           rew_neq_in Htls0. rewrite map_get_set in Htls0.
           injection Htls0 as Heqtls0. subst tls0.
           do 5 eexists. split; eauto.
           unfold joinsig in Hjoin; jeat.
        -- unfold ex_free_tsk in *.
           destruct Hf as (fts0 & tids0 & Hfts0 & Hgettids0 & Hin).
           rewrite map_get_set in Hfts0.
           injection Hfts0 as Heqfts0. subst fts0.
           casetac dc domx He Hne.
           ++ subst domx. rewrite map_get_set in Hgettids0.
              injection Hgettids0 as Heqtids0. subst tids0.
              apply in_app_or in Hin. destruct Hin as [Hin | Hin].
              ** right. unfold ex_free_tsk. do 2 eexists; splits; eauto.
              ** simpl in Hin. destruct Hin as [Heq | Hfalse]; tryfalse.
                 subst tx. left. unfold ex_active_tsk.
                 do 5 eexists; split; eauto.
           ++ rewrite neq_set_get in Hgettids0; auto.
              right. unfold ex_free_tsk. do 2 eexists; splits; eauto.
Qed.


Lemma dr_taskdel:
  forall vl t, 
    tl_vl_match (Tint8 :: nil) vl = true -> 
    deduct_rules t (rly_tsk_env t) (guar_tsk_env t) flows_to obsr_equiv_data
      (task_apispecs.taskdel vl) q_star. 
Proof.
  introv Htvm.
  eapply seq_rule with (q' := tdel_release_post vl).
  -
    constructors.
    + 
      apply stable_pre_trivial_asrt.
    +
      introv Hpre1 Htdel.
      splits.
      * unfolds.
        splits.
        ** 
          eapply tdel_release_post_sat; eauto.
        **
          eapply taskdel_tcb_release_prsv_inv; eauto.
        ** eapply taskdel_tcb_release_guar; eauto.
      *
        eapply taskdel_tcb_release_sdom_iff; eauto.
      *
        introv Hf.
        unfolds in Htdel.
        do 3 (d_mt_hyp; (try inv_errp; tryfalse)).
        do 2 (d_if_hyp; (try inv_errp; tryfalse)).
        rn_or Hor.
        destruct Hor; simpljoin; try inv_errp; tryfalse.
        inv_errp; tryfalse. 
      *
        (* integrity oblig. *)
        introv Hnex Hsd Hnfl.
        eapply tdel_obsr_equiv_data; eauto.
    +
      (* confidentiality oblig. *)
      introv Hpre2 Hdel1 Hdel2 Hnex1 Hnex2.
      eapply tdel2_obsr_equiv_data_prsv; eauto.
  -
    introv Hinv Hpost Hs2.
    d_mt_hyp.
    + unfolds in Hpost. simpljoin. false.
    + d_mt_hyp; 
        try (unfolds in Hpost; simpljoin; tryfalse; fail).
      unfolds in Hpost.
      destruct Hpost as (i0 & Heq_vint).
      inverts Heq_vint.
      subst.
      destruct (Int.eq i0 Int.mone) eqn: E.
      * simpl.
        split.
        ** unfolds. auto.
        **
          {
            constructors.
            + eapply dr_sched; eauto.
            + introv Hi Hq_ Hs2.
              subst s2.
              split.
              * apply ssp_end.
              * constructors. 
          }
      *
        split.
        **
          apply ssp_end; eauto.
        **
          constructors.
Qed.

      
         
