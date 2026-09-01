
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

Definition tcre_alloc_post (vl: vallist) (t: tid) (vl': vallist) (O: osabst) :=                
  (exists t_n, vl' = Vint32 Int.mone :: Vptr t_n :: nil) \/ 
    (exists i, i <> Int.mone /\ vl' = Vint32 i :: nil). 

Lemma tcre_alloc_sat_post:
  forall t vl O ac vl' O', 
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    tcre_alloc_post vl t vl' O'.
Proof.
  introv Halloc.
  unfolds in Halloc.
  d_mt_hyp.
  - inv_errp.
    simpl in H.
    subst.
    simpl.
    unfolds.
    right.
    eexists; splits; eauto.
    introv Hf; inverts Hf.
  - assert (Hor: (exists fn, v = Vptr fn) \/ ~exists fn, v = Vptr fn) by tauto.
    destruct Hor as [Hptr | Hnptr].
    +
      destruct Hptr as (fn & Hv).
      subst v.
      assert (Hor: (exists arg pr, v0 = Vptr arg :: Vint32 pr :: nil)
                   \/ ~exists arg pr, v0 = Vptr arg :: Vint32 pr :: nil) by tauto.
      destruct Hor as [Hex | Hnex].
      *
        destruct Hex as (arg & pr & Hv0).
        subst v0.
        d_if_hyp.
        **
          inv_errp. simpl in *. simpljoin.
          unfolds.
          right.
          eexists; splits; eauto.
          introv Hf; inverts Hf.
        **
          simpljoin.
          rn_or Hor.
          destruct Hor as [Hepr | Hnepr].
          *** simpljoin.
              inv_errp. simpl in *. simpljoin.
              unfolds.
              right.
              eexists; splits; eauto.
              introv Hf; inverts Hf.
          ***
            simpljoin.
            d_mt_hyp.
            {
              inv_errp.
              unfolds.
              right.
              eexists; splits; eauto.
              introv Hf; inverts Hf.
            }
            {
              simpljoin.
              unfolds.
              left.
              eexists; eauto.
            }
      *
        assert (Herrp: err_prop MODEL_ERR_PARAMS (fst (vl', O')) O (snd (vl', O')) ac).
        {
          do 5 (d_mt_hyp; simpl in Halloc; auto).
          false. apply Hnex; do 2 eexists; eauto.
        }
        inv_errp. simpl in *. simpljoin.
        unfolds.
        right.
        eexists; splits; eauto.
        introv Hf; inverts Hf.
    +
      assert (Herrp: err_prop MODEL_ERR_PARAMS (fst (vl', O')) O (snd (vl', O')) ac).
      {
          do 2 (d_mt_hyp; simpl in Halloc; auto).
          false. apply Hnptr; do 2 eexists; eauto.
      }
      inv_errp. simpl in *. simpljoin.
      unfolds.
      right.
      eexists; splits; eauto.
      introv Hf; inverts Hf.
Qed. 

Lemma tcre_alloc_newtsk_same_dom:
  forall t vl O ac vl' O' a1 a2 t' 
         (Hpre1 : pre1 t O trivial_asrt)
         (Halloc : task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O'))
         (Hac : ac = _TCreAct t' a1 a2), 
    t <> t' /\ (forall td : task_dom, sdom O t td <-> sdom O t' td). 
Proof.
  intros.
  unfolds in Halloc.
  d_mt_hyp.
  - inv_errp.
  - do 6 (d_mt_hyp; (try inv_errp; simpljoin; tryfalse)).
    d_if_hyp; (try (inv_errp; simpljoin; tryfalse; fail)).
    destruct Halloc as (tls & pr_c & st_c & msg_c & sus_c & d_c & ts & Hgtls & Hgt & Hor).
    destruct Hor as [Hex_pr | Hnex_pr].
    + simpljoin; (try inv_errp; simpljoin; tryfalse).
    + destruct Hnex_pr as (Hnexp & Hex).
      destruct Hex as (tsmp & Hgtsmp & Hgfts & Hmt).
      d_mt_hyp; (try inv_errp; simpljoin; tryfalse).
      inv_hctr _TCreAct.
      destruct Hpre1 as (Hp1 & Hinv1).
      assert (Hinv_ := Hinv1).
      inverts Hinv1.
      assert (Heat: ex_active_tsk O t d_c).
      {
        unfolds.
        do 5 eexists; splits; eauto.
      }
      assert (Heft: ex_free_tsk O t0 d_c).
      {
        unfolds.
        do 2 eexists; splits; eauto.
        simpl; left; auto.
      }
      assert (Hsdt: sdom O t d_c).
      {
        unfolds. unfold state.
        unfolds. eauto.
      }
      assert (Hsdt0: sdom O t0 d_c).
      {
        unfolds. unfold state.
        unfolds. eauto.
      }
      casetac t t0 He Hne.
      * subst.
        lets Hf: inv_tsk_af_disj Heat Heft.
        false.
      *
        split; auto.
        intros.
        split; introv Hsd.
        **
          assert (td = d_c).
          {
            pose proof sdom_is_fn as H_.
            lets H__: H_ Hinv_ Hsdt Hsd.
            eauto.
          }
          subst.
          auto.
        **
          assert (td = d_c).
          {
            pose proof sdom_is_fn as H_.
            lets H__: H_ Hinv_ Hsdt0 Hsd.
            eauto.
          }
          subst.
          auto.
Qed. 

Lemma err_prop_obsr_equiv: 
  forall vl' O O' ac d z, 
    err_prop z vl' O O' ac -> obsr_equiv_data d O O'. 
Proof.
  introv Herr.
  inv_errp.
  destruct d.
  - simpl.
    apply obsr_equiv_tskd_refl.
  - apply obsr_equiv_data_refl.
Qed. 

Lemma alloc_obsr_equiv_tasks: 
  forall t O tls pr_c st_c msg_c sus_c d_c i prio txmp t0 ts0
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr_c, st_c, msg_c, sus_c, d_c))
         (Hnexp : ~ (exists t' st msg0 sus, get tls t' = Some (prio, st, msg0, sus, d_c)))
         (Hgtsmp : get O freetid = Some (freetidlist txmp))
         (Hgfts : get txmp d_c = Some (t0 :: ts0))
         (Hsd : sdom O t d_c)
         (Hne : d_c <> i), 
    obsr_equiv_tasks i O
      (set (set O abstcblsid (abstcblist (set tls t0 (prio, rdy, Vnull, false, d_c))))
         freetid (freetidlist (set txmp d_c ts0))).
Proof.
  intros.
  unfolds.
  split.
  - rew_neq. rewrite map_get_set.
    split; intros; eexists; eauto.
  -
    introv Hg1 Hg2.
    destruct Hpre1 as (Hp & Hinv).
    rew_neq_in Hg2.
    rewrite map_get_set in Hg2.
    inverts Hg2.
    uni_12_sym (get O abstcblsid).
    split.
    + 
      unfold ex_tsk_in_dom.
      casetac t0 t1 He Hf.
      * subst.
        rewrite map_get_set.
        split; introv Hex.
        ** destruct Hex as (pr_ & st_ & m_ & sus_ & Hgt1).
           assert (Hinv_ := Hinv).
           inverts Hinv.
           assert (Hsdc: sdom_ O t1 d_c).
           {
             unfolds. right.
             unfolds.
             do 2 eexists; splits; eauto.
             left; auto.
           }
           assert (Hsdi: sdom_ O t1 i).
           {
             unfolds. left.
             unfolds.
             do 5 eexists; splits; eauto.
           }
           pose proof sdom_is_fn as Hsif.
           lets H__: Hsif Hinv_ Hsdc Hsdi.
           false.
        **
          simpljoin.
          inverts H.
          false.
      *
        rew_neq.
        tauto.
    +
      introv Hg1 Hg2 Hdi.
      casetac t0 t1 He_ Hne_.
      * subst.
        rewrite map_get_set in Hg2.
        inverts Hg2.
        rename d2 into td.
        assert (Hsdc: sdom_ O t1 td).
        {
          unfolds. right.
          unfolds.
          do 2 eexists; splits; eauto.
          left; auto.
        }
        assert (Hsdi: sdom_ O t1 i).
        {
          unfolds. left.
          unfolds.
          do 5 eexists; splits; eauto.
        }
        pose proof sdom_is_fn as Hsif.
        lets H__: Hsif Hinv Hsdc Hsdi.
        false.
      *
        rew_neq_in Hg2.
        Set Printing Implicit.
        unfold msg in Hg1. unfold sus_st in Hg1.
        rewrite Hg1 in Hg2.
        inverts Hg2.
        Unset Printing Implicit.
        splits;auto.
Qed. 

Lemma alloc_obsr_equiv_freetids:
  forall t O txmp d_c t0 ts0 i prio tls
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtsmp : get O freetid = Some (freetidlist txmp))
         (Hgfts : get txmp d_c = Some (t0 :: ts0))
         (Hsd : sdom O t d_c)
         (Hne : d_c <> i), 
    obsr_equiv_freetids i O
      (set (set O abstcblsid (abstcblist (set tls t0 (prio, rdy, Vnull, false, d_c))))
         freetid (freetidlist (set txmp d_c ts0))). 
Proof.
  intros.
  unfolds.
  rewrite map_get_set.
  split.
  - 
    split.
    + introv Hex.
      eexists; eauto.
    + introv Hex.
      destruct Hex as (fts & Heq).
      inverts Heq.
      eexists; eauto.
  -
    introv Hg1 Hg2.
    inverts Hg2.
    rew_neq.
    rewrite Hgtsmp in Hg1.
    inverts Hg1.
    tauto.
Qed.       

Lemma alloc_obsr_equiv_tskd: 
  forall t O tls pr_c st_c msg_c sus_c d_c i prio txmp t0 ts0
         (Hpre1 : pre1 t O trivial_asrt)
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr_c, st_c, msg_c, sus_c, d_c))
         (Hnexp : ~ (exists t' st msg0 sus, get tls t' = Some (prio, st, msg0, sus, d_c)))
         (Hgtsmp : get O freetid = Some (freetidlist txmp))
         (Hgfts : get txmp d_c = Some (t0 :: ts0))
         (Hsd : sdom O t d_c)
         (Hne : d_c <> i), 
    obsr_equiv_tskd i O
      (set (set O abstcblsid (abstcblist (set tls t0 (prio, rdy, Vnull, false, d_c))))
         freetid (freetidlist (set txmp d_c ts0))). 
Proof.
  intros.
  constructors.
  -
    eapply alloc_obsr_equiv_tasks; eauto.
  -
    eapply obsr_equiv_mqs_nochange; eauto.
    repeat rew_neq.
  -
    eapply obsr_equiv_chs_nochange; eauto.
    repeat rew_neq.
  -
    eapply alloc_obsr_equiv_freetids; eauto.
  -
    eapply obsr_equiv_fqs_nochange; eauto.
    repeat rew_neq. 
Qed. 

Lemma tcre_alloc_obsr_equiv_data:
  forall vl t O ac vl' O' td d
         (Htvm : tl_vl_match (Tptr Tvoid :: Tptr Tvoid :: Tint8 :: nil) vl = true)
         (Hpre1 : pre1 t O trivial_asrt)
         (Halloc : task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O'))
         (Hsd : sdom O t td)
         (Hnfl : ~ flows_to (TaskDom td) d), 
    obsr_equiv_data d O O'. 
Proof.
  intros. 
  unfolds in Halloc.
  do 7
    (d_mt_hyp;
     try (simpl in Htvm; simpljoin; tryfalse;
          eapply err_prop_obsr_equiv; eauto; fail)).
  d_if_hyp.
  -
    simpl in Halloc. eapply err_prop_obsr_equiv; eauto.
  -
    subst. 
    destruct Halloc as (tls & pr_c & st_c & msg_c & sus_c & d_c & ts & Hgtls & Hgt & Hor).
    rename i  into prio.
    destruct Hor as [Hexp | Hnexp].
    + destruct Hexp.
      eapply err_prop_obsr_equiv; eauto.
    +
      destruct Hnexp as (Hnexp & txmp & Hgtsmp & Hgfts & Hmt).
      d_mt_hyp.
      *
        eapply err_prop_obsr_equiv; eauto.
      *
        simpljoin; subst.
        rename l into ts0.
        lets H__: tls_sdom_td_eq Hpre1 Hgtls Hgt Hsd.
        subst td.
        destruct d.
        **
          casetac d_c i He Hne.
          *** subst.
              false. 
              apply Hnfl.
              constructors.
          ***
            simpl.   
            eapply alloc_obsr_equiv_tskd; eauto.  
        **
          (* SchedDom *)
          constructors; try repeat rew_neq.
Qed. 


Lemma obsr_equiv_fts_eq:
  forall td O1 O2 tsmp1 tsmp2 ts1 ts2, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 freetid = Some (freetidlist tsmp1) ->
    get O2 freetid = Some (freetidlist tsmp2) ->
    get tsmp1 td = Some ts1 ->
    get tsmp2 td = Some ts2 ->
    ts1 = ts2.  
Proof.
  introv Hdte Htsmp1 Htsmp2 Hts1 Hts2.
  simpl in Hdte.
  inverts Hdte.
  unfolds in oe_td_fts.
  destruct oe_td_fts as (Heqv & Hall).
  lets H_: Hall Htsmp1 Htsmp2.
  eapply H_ in Hts1; eauto.
  rewrite Hts1 in Hts2.
  inverts Hts2.
  auto.
Qed. 

Lemma tcre_alloc2_obsr_equiv_tasks_prsv:
  forall t O1 O2 td td' tls1 tls2 tsmp1 tsmp2 pr_c st_c msg_c sus_c t0 ts  pr 
         (Hpre11 : pre1 t O1 trivial_asrt)
         (Hpre12 : pre1 t O2 trivial_asrt)
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr_c, st_c, msg_c, sus_c, td'))
         (Hgtsmp1 : get O1 freetid = Some (freetidlist tsmp1))
         (Hgts1 : get tsmp1 td' = Some (t0 :: ts))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr_c, st_c, msg_c, sus_c, td'))
         (Hgtsmp2 : get O2 freetid = Some (freetidlist tsmp2))
         (Hgts2 : get tsmp2 td' = Some (t0 :: ts))
         (Hflt : flows_to (TaskDom td') (TaskDom td)), 
    obsr_equiv_tasks td
      (set (set O1 abstcblsid (abstcblist (set tls1 t0 (pr, rdy, Vnull, false, td'))))
         freetid (freetidlist (set tsmp1 td' ts)))
      (set (set O2 abstcblsid (abstcblist (set tls2 t0 (pr, rdy, Vnull, false, td'))))
         freetid (freetidlist (set tsmp2 td' ts))). 
Proof.
  intros.
  unfolds.
  rew_neq. rewrite map_get_set.
  rew_neq. rewrite map_get_set.
  splits.
  -
    split; introv Hex; eexists; eauto.
  -
    introv Hg1 Hg2.
    symmetry in Hg1. inverts Hg1.
    symmetry in Hg2. inverts Hg2.
    split.
    + unfold ex_tsk_in_dom.
      casetac t0 t1 He Hne.
      * subst.
        rewrite map_get_set.
        rewrite map_get_set.
        split.
        ** introv Hex.
           destruct Hex as (pr0 & st & m & sus & Heq).
           inverts Heq.
           do 4 eexists; eauto.
        **
          introv Hex.
          destruct Hex as (pr0 & st & m & sus & Heq).
          inverts Heq.
          do 4 eexists; eauto.
      *
        do 2 rew_neq.
        eapply dte_ex_tsk_in_dom_same; eauto.
    +
      introv Hg1 Hg2.
      introv Hd.
      casetac t0 t1 He Hne.
      * subst.
        rewrite map_get_set in Hg1.
        rewrite map_get_set in Hg2.
        inverts Hg1. inverts Hg2.
        splits; eauto.
      *
        rew_neq_in Hg1.
        rew_neq_in Hg2.
        subst d1.
        lets H_: dte_ex_tsk_in_dom_same t1 Hdte Hgtls1 Hgtls2.
        assert (Hex: exists pr0 st m sus0, get tls1 t1 = Some (pr0, st, m, sus0, td)).
        {
          do 4 eexists; eauto.
        }
        eapply H_ in Hex.
        destruct Hex as (pr0 & st & m & sus & Hget).
        Set Printing Implicit.
        unfold msg in Hget.
        unfold sus_st in Hget.
        rewrite Hg2 in Hget.
        inverts Hget.
        Unset Printing Implicit.
        clear H_.
        eapply obsr_equiv_data_tsk_eq with (t:=t1) (td:=td); eauto.
Qed.         
        
Lemma tcre_alloc2_obsr_equiv_freetids_prsv:
  forall t O1 O2 td td' tsmp1 tsmp2 t0 ts pr tls1 tls2
         (Hpre11 : pre1 t O1 trivial_asrt)
         (Hpre12 : pre1 t O2 trivial_asrt)
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgtsmp1 : get O1 freetid = Some (freetidlist tsmp1))
         (Hgts1 : get tsmp1 td' = Some (t0 :: ts))
         (Hgtsmp2 : get O2 freetid = Some (freetidlist tsmp2))
         (Hgts2 : get tsmp2 td' = Some (t0 :: ts)), 
    (* Hflt : flows_to (TaskDom td') (TaskDom td) *)
    obsr_equiv_freetids td
      (set (set O1 abstcblsid (abstcblist (set tls1 t0 (pr, rdy, Vnull, false, td'))))
         freetid (freetidlist (set tsmp1 td' ts)))
      (set (set O2 abstcblsid (abstcblist (set tls2 t0 (pr, rdy, Vnull, false, td'))))
         freetid (freetidlist (set tsmp2 td' ts))). 
Proof.
  intros.
  unfolds.
  do 2 rewrite map_get_set.
  split.
  - split; introv Hex; eexists; eauto.
  - introv Hg1 Hg2.
    inverts Hg1.
    inverts Hg2.
    casetac td' td He Hne.
    + subst.
      do 2 rewrite map_get_set.
      tauto.
    + do 2 rew_neq.
      simpl in Hdte.
      eapply Hdte; eauto.
Qed.     

Lemma tcre_alloc2_obser_equiv_tskd_prsv:
  forall t O1 O2 td td' tls1 tls2 tsmp1 tsmp2 pr_c1 st_c1 msg_c1 sus_c1 pr_c2 st_c2 msg_c2 sus_c2 t0 ts  pr
         (Hpre11 : pre1 t O1 trivial_asrt)
         (Hpre12 : pre1 t O2 trivial_asrt)
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hgtls1 : get O1 abstcblsid = Some (abstcblist tls1))
         (Hgt1 : get tls1 t = Some (pr_c1, st_c1, msg_c1, sus_c1, td'))
         (Hgtsmp1 : get O1 freetid = Some (freetidlist tsmp1))
         (Hgts1 : get tsmp1 td' = Some (t0 :: ts))
         (Hgtls2 : get O2 abstcblsid = Some (abstcblist tls2))
         (Hgt2 : get tls2 t = Some (pr_c2, st_c2, msg_c2, sus_c2, td'))
         (Hgtsmp2 : get O2 freetid = Some (freetidlist tsmp2))
         (Hgts2 : get tsmp2 td' = Some (t0 :: ts))
         (Hflt : flows_to (TaskDom td') (TaskDom td)), 
    (* Hnext : ~ (exists t' st msg0 sus, get tls1 t' = Some (i, st, msg0, sus, td')) *)

    obsr_equiv_tskd td
      (set (set O1 abstcblsid (abstcblist (set tls1 t0 (pr, rdy, Vnull, false, td')))) freetid
         (freetidlist (set tsmp1 td' ts)))
      (set (set O2 abstcblsid (abstcblist (set tls2 t0 (pr, rdy, Vnull, false, td')))) freetid
         (freetidlist (set tsmp2 td' ts))).
Proof.
  intros.
  lets H_: obsr_equiv_data_tsk_eq Hdte' Hgtls1 Hgtls2 Hgt1 Hgt2.
  simpljoin.
  rename pr_c2 into pr_c.
  rename st_c2 into st_c.
  rename msg_c2 into msg_c.
  rename sus_c2 into sus_c.
  constructors.
  -
    eapply tcre_alloc2_obsr_equiv_tasks_prsv; eauto.
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
    eapply tcre_alloc2_obsr_equiv_freetids_prsv; eauto.
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







Lemma taskcre_tcb_alloc_guar:
  forall t vl O ac vl' O',
    pre1 t O trivial_asrt ->
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    guar_tsk_env t O O'.
Proof.
  introv Hpre Halloc.
  destruct Hpre as (Htriv & Hinv).
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp. apply guar_tsk_refl.
  - do 6 (d_mt_hyp; try (inv_errp; apply guar_tsk_refl)).
    d_if_hyp.
    + inv_errp. apply guar_tsk_refl.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp. apply guar_tsk_refl.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp. apply guar_tsk_refl.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           assert (Hfree_tn : ex_free_tsk O tn dc).
           { unfold ex_free_tsk. do 2 eexists; splits; eauto.
             simpl; auto. }
           unfold guar_tsk_env. split.
           ++ introv Hneq Hsd. unfold sdom, state in *.
              destruct Hsd as [Ha | Hf].
              ** left. unfold ex_active_tsk in *.
                 destruct Ha as (tls0 & pr0 & st0 & msg0 & sus0 & Htls0 & Hg0).
                 rewrite Hgtls in Htls0. inverts Htls0.
                 casetac tn t' He Hne.
                 --- subst.
                     assert (Hsda : sdom_ O t' td).
                     { left. unfold ex_active_tsk. do 5 eexists; splits; eauto. }
                     assert (td = dc).
                     { eapply Hinv.(inv_tsk_d_disj).
                       - exact Hsda.
                       - right; exact Hfree_tn. }
                     subst td. exfalso.
                     eapply Hinv.(inv_tsk_af_disj) with (t := t') (td := dc).
                     { unfold ex_active_tsk. do 5 eexists; splits; eauto. }
                     { exact Hfree_tn. }
                 --- exists (set tls0 tn (i, rdy, Vnull, false, dc)).
                     exists pr0. exists st0. exists msg0. exists sus0.
                     Set Printing Implicit. unfold tid in Hg0 |- *.
                     split.
                     { rewrite neq_set_get.
                       2: { introv Hx; inverts Hx. }
                       rewrite map_get_set. reflexivity. }
                     { rewrite neq_set_get.
                       2: { apply not_eq_sym; exact Hne. }
                       exact Hg0. }
                     Unset Printing Implicit.
              ** casetac tn t' He Hne.
                 --- subst.
                     assert (td = dc).
                     { eapply Hinv.(inv_tsk_d_disj).
                       - right; exact Hf.
                       - right; exact Hfree_tn. }
                     subst td. left. unfold ex_active_tsk. do 5 eexists; split.
                     { assert (Hab : abstcblsid <> freetid)
                         by (introv Hx; inverts Hx).
                       rewrite neq_set_get; auto.
                       rewrite map_get_set; auto. }
                     { rewrite map_get_set; auto. }
                 --- right. unfold ex_free_tsk in *.
                     destruct Hf as (fts & tids & Hfts & Hgd & Hin).
                     rewrite Hgfts in Hfts. inverts Hfts.
                     casetac dc td Heq Hneqd.
                     { subst. rewrite Hgts in Hgd. inverts Hgd.
                       exists (set fts td ts0). exists ts0.
                       split. { rewrite map_get_set; auto. }
                       rewrite map_get_set. split; auto.
                       simpl in Hin. destruct Hin as [He | Hin].
                       - subst; contradiction.
                       - exact Hin. }
                     { exists (set fts dc ts0). exists tids.
                       split. { rewrite map_get_set; auto. }
                       rewrite neq_set_get.
                       { split; [exact Hgd | exact Hin]. }
                       { apply not_eq_sym; exact Hneqd. } }
           ++ introv Hqsd. destruct Hqsd as [Ha | Hf].
              ** left. unfold ex_active_que in *.
                 repeat rew_neq.
              ** right. unfold ex_free_que in *.
                 repeat rew_neq.
Qed.

Lemma taskcre_tcb_alloc_sdom_iff:
  forall t vl O ac vl' O',
    pre1 t O trivial_asrt ->
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    forall t0 td, sdom O t0 td <-> sdom O' t0 td.
Proof.
  introv Hpre Halloc.
  assert (Hguar : guar_tsk_env t O O').
  { eapply taskcre_tcb_alloc_guar; eauto. }
  destruct Hpre as (Htriv & Hinv).
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp. intros; split; auto.
  - do 6 (d_mt_hyp;
           try (inv_errp; intros; split; auto; fail)).
    d_if_hyp.
    + inv_errp. intros; split; auto.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp. intros; split; auto.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp. intros; split; auto.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           assert (Hfree_tn : ex_free_tsk O tn dc).
           { unfold ex_free_tsk. do 2 eexists; splits; eauto. simpl; auto. }
           assert (Htne : t <> tn).
           {
             intro He; subst tn.
             eapply Hinv.(inv_tsk_af_disj) with (t := t) (td := dc).
             - unfold ex_active_tsk. do 5 eexists; splits; eauto.
             - exact Hfree_tn.
           }
           intros t0 td. split; intro Hsd.
           ++ casetac t t0 He Hne.
              ** subst t0.
                 assert (td = dc).
                 {
                   eapply Hinv.(inv_tsk_d_disj).
                   - exact Hsd.
                   - left. unfold ex_active_tsk.
                     do 5 eexists; splits; eauto.
                 }
                 subst td. unfold sdom, state. left.
                 unfold ex_active_tsk.
                 exists (set tls tn (i, rdy, Vnull, false, dc)).
                 exists prc. exists stc. exists msgc. exists susc. split.
                 --- rewrite neq_set_get.
                     2: { introv Hx; inverts Hx. }
                     rewrite map_get_set. reflexivity.
                 --- rewrite neq_set_get.
                     { exact Hgt. }
                     { exact Htne. }
              ** unfold guar_tsk_env in Hguar.
                 destruct Hguar as (Hgtsk & Hgq).
                 eapply Hgtsk; eauto.
           ++ unfold sdom, state in *.
              destruct Hsd as [Ha | Hf].
              ** unfold ex_active_tsk in Ha.
                 destruct Ha as
                     (tls0 & pr0 & st0 & msg0 & sus0 & Htls0 & Hget0).
                 rew_neq_in Htls0. rewrite map_get_set in Htls0.
                 inverts Htls0.
                 casetac tn t0 He Hne.
                 --- subst. rewrite map_get_set in Hget0. inverts Hget0.
                     right; exact Hfree_tn.
                 --- left. unfold ex_active_tsk.
                     rewrite neq_set_get in Hget0; eauto.
                     exists tls. exists pr0. exists st0. exists msg0. exists sus0.
                     split; eauto.
              ** right. unfold ex_free_tsk in *.
                 destruct Hf as (fts & tids & Hfts & Hgd & Hin).
                 rewrite map_get_set in Hfts. inverts Hfts.
                 casetac dc td He Hne.
                 --- subst. rewrite map_get_set in Hgd. inverts Hgd.
                     exists tsmp. exists (tn :: tids). splits; eauto.
                     simpl; auto.
                 --- exists tsmp. exists tids. splits; eauto.
                     rewrite neq_set_get in Hgd; eauto.
Qed.
  
Lemma taskcre_tcb_alloc_tsk_af_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    tsk_active_free_disj O ->
    tsk_active_free_disj O'.
Proof.
  introv Halloc Haf.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; auto.
  - do 6 (d_mt_hyp; try (inv_errp; auto; fail)).
    d_if_hyp.
    + inv_errp; auto.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; auto.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; auto.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           unfold tsk_active_free_disj in *.
           introv Hactive Hfree.
           unfold ex_active_tsk in Hactive.
           destruct Hactive as
               (tls0 & pr0 & st0 & msg0 & sus0 & Htls0 & Hget0).
           rewrite neq_set_get in Htls0; eauto.
           2: { introv Hx; inverts Hx. }
           rewrite map_get_set in Htls0. inverts Htls0.
           unfold ex_free_tsk in Hfree.
           destruct Hfree as (fts & tids & Hfts & Hgd & Hin).
           rewrite map_get_set in Hfts. inverts Hfts.
           casetac tn t0 He Hne.
           ++ subst. rewrite map_get_set in Hget0. inverts Hget0.
              rewrite map_get_set in Hgd. inverts Hgd.
              exact (Hnotin Hin).
           ++ rewrite neq_set_get in Hget0; eauto.
              assert (Hactive0 : ex_active_tsk O t0 td).
              {
                unfold ex_active_tsk.
                exists tls. exists pr0. exists st0. exists msg0. exists sus0.
                split; eauto.
              }
              assert (Hfree0 : ex_free_tsk O t0 td).
              {
                unfold ex_free_tsk.
                casetac dc td Hed Hned.
                - subst. rewrite map_get_set in Hgd. inverts Hgd.
                  exists tsmp. exists (tn :: tids). splits; eauto.
                  simpl; auto.
                - exists tsmp. exists tids. splits; eauto.
                  rewrite neq_set_get in Hgd; eauto.
              }
              eapply Haf; eauto.
Qed.
Lemma taskcre_tcb_alloc_tsk_dom_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    I O ->
    tsk_dom_disj O'.
Proof.
  introv Halloc Hinv.
  assert (Hpre : pre1 t O trivial_asrt).
  {
    split; auto.
    unfold trivial_asrt; auto.
  }
  unfold tsk_dom_disj.
  introv Hsd1 Hsd2.
  pose proof (@taskcre_tcb_alloc_sdom_iff
                t vl O ac vl' O' Hpre Halloc t0 td1) as Hiff1.
  pose proof (@taskcre_tcb_alloc_sdom_iff
                t vl O ac vl' O' Hpre Halloc t0 td2) as Hiff2.
  apply Hinv.(inv_tsk_d_disj) with (t := t0).
  - apply Hiff1; exact Hsd1.
  - apply Hiff2; exact Hsd2.
Qed.

Lemma taskcre_tcb_alloc_tsk_diff_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    tsk_diff_id_prio O ->
    tsk_diff_id_prio O'.
Proof.
  introv Halloc Hdiff.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; auto.
  - do 6 (d_mt_hyp; try (inv_errp; auto; fail)).
    d_if_hyp.
    + inv_errp; auto.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; auto.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; auto.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           unfold tsk_diff_id_prio in *.
           rewrite neq_set_get.
           2: { introv Hx; inverts Hx. }
           rewrite map_get_set.
           introv Heqtls Hneq Hg1 Hg2. inverts Heqtls.
           casetac tn t1 He1 Hne1.
           ++ subst. rewrite map_get_set in Hg1. inverts Hg1.
              rewrite neq_set_get in Hg2; eauto.
              intro Heqpr. apply Hnprio.
              exists t2. exists st2. exists msg2. exists sus2.
              rewrite  Heqpr. exact Hg2.
           ++ rewrite neq_set_get in Hg1; eauto.
              casetac tn t2 He2 Hne2.
              ** subst. rewrite map_get_set in Hg2. inverts Hg2.
                 intro Heqpr. apply Hnprio.
                 exists t1. exists st1. exists msg1. exists sus1.
                 rewrite <-Heqpr. exact Hg1.
              ** rewrite neq_set_get in Hg2; eauto.
Qed.

Lemma taskcre_tcb_alloc_que_af_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    que_active_free_disj O ->
    que_active_free_disj O'.
Proof.
  introv Halloc Haf.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; auto.
  - do 6 (d_mt_hyp; try (inv_errp; auto; fail)).
    d_if_hyp.
    + inv_errp; auto.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; auto.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; auto.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           eapply same_mqs_que_active_free_disj with (O := O); eauto.
           all: repeat rew_neq.
Qed.

Lemma taskcre_tcb_alloc_que_dom_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    que_dom_disj O ->
    que_dom_disj O'.
Proof.
  introv Halloc Hdom.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; auto.
  - do 6 (d_mt_hyp; try (inv_errp; auto; fail)).
    d_if_hyp.
    + inv_errp; auto.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; auto.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; auto.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           eapply same_mqs_que_dom_disj with (O := O); eauto.
           all: repeat rew_neq.
Qed.
Lemma taskcre_tcb_alloc_mq_wt_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    I O ->
    mq_wt_cond O'.
Proof.
  introv Halloc Hinv.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; apply Hinv.
  - do 6 (d_mt_hyp; try (inv_errp; apply Hinv; fail)).
    d_if_hyp.
    + inv_errp; apply Hinv.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; apply Hinv.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; apply Hinv.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           assert (Hfree_tn : ex_free_tsk O tn dc).
           { unfold ex_free_tsk. do 2 eexists; splits; eauto. simpl; auto. }
           assert (Hnone : get tls tn = None).
           {
             remember (get tls tn) as got eqn:Hget.
             destruct got.
             2: { reflexivity. }
             assert (Hexactive : exists dn, ex_active_tsk O tn dn).
             {
               repeat match goal with
                      | x : (_ * _)%type |- _ => destruct x
                      end.
               eexists. unfold ex_active_tsk.
               do 5 eexists; splits; eauto.
             }
             destruct Hexactive as (dn & Hactive).
             assert (dn = dc).
             {
               eapply Hinv.(inv_tsk_d_disj) with (t := tn).
               - left; exact Hactive.
               - right; exact Hfree_tn.
             }
             subst dn. exfalso.
             eapply Hinv.(inv_tsk_af_disj); eauto.
           }
           unfold mq_wt_cond.
           introv Hgqls Hgtls' Hgq Hin.
           repeat rew_neq_in Hgqls.
           rewrite neq_set_get in Hgtls'; eauto.
           2: { introv Hx; inverts Hx. }
           rewrite map_get_set in Hgtls'. inverts Hgtls'.
           lets Hw: Hinv.(inv_mq_wt) Hgqls Hgtls Hgq Hin.
           destruct Hw as (pr0 & msg0 & sus0 & to & Hgetw).
           casetac tn t0 He Hne.
           ++ subst. rewrite Hnone in Hgetw. inverts Hgetw.
           ++ do 4 eexists. rewrite neq_set_get; eauto.
Qed.

Lemma taskcre_tcb_alloc_wt_mq_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    I O ->
    wt_mq_cond O'.
Proof.
  introv Halloc Hinv.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; apply Hinv.
  - do 6 (d_mt_hyp; try (inv_errp; apply Hinv; fail)).
    d_if_hyp.
    + inv_errp; apply Hinv.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; apply Hinv.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; apply Hinv.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           unfold wt_mq_cond.
           introv Hgtls' Hgett Hgqls.
           rewrite neq_set_get in Hgtls'; eauto.
           2: { introv Hx; inverts Hx. }
           rewrite map_get_set in Hgtls'. inverts Hgtls'.
           repeat rew_neq_in Hgqls.
           casetac tn t0 He Hne.
           ++ subst. rewrite map_get_set in Hgett. inverts Hgett.
           ++ rewrite neq_set_get in Hgett; eauto.
              eapply Hinv.(inv_wt_mq); eauto.
Qed.
Lemma taskcre_tcb_alloc_chcfg_prsv:
  forall t vl O ac vl' O',
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    chs_sat_config O ->
    chs_sat_config O'.
Proof.
  introv Halloc Hcfg.
  unfold task_apispecs.taskcre_tcb_alloc in Halloc.
  d_mt_hyp.
  - inv_errp; auto.
  - do 6 (d_mt_hyp; try (inv_errp; auto; fail)).
    d_if_hyp.
    + inv_errp; auto.
    + destruct Halloc as
          (tls & prc & stc & msgc & susc & dc & ts &
           Hgtls & Hgt & Hor).
      destruct Hor as [Hex | Hnew].
      * destruct Hex as (Hex & Herr). inv_errp; auto.
      * destruct Hnew as (Hnprio & tsmp & Hgfts & Hgts & Hmt).
        destruct ts; simpl in Hmt.
        -- inv_errp; auto.
        -- rename t0 into tn. rename ts into ts0.
           destruct Hmt as (Hnotin & HO' & Hac & Hvl'). subst O'.
           eapply same_chs_chs_sat_config with (O := O); eauto.
           repeat rew_neq.
Qed.

Lemma taskcre_tcb_alloc_prsv_inv:
  forall t vl O ac vl' O',
    pre1 t O trivial_asrt ->
    task_apispecs.taskcre_tcb_alloc t vl O ac (vl', O') ->
    I O'.
Proof.
intros.
  inverts H. inverts H2.
  constructors.
  + eapply taskcre_tcb_alloc_tsk_af_prsv; eauto.
  + eapply taskcre_tcb_alloc_tsk_dom_prsv; eauto.
      constructor; eauto.
  + eapply taskcre_tcb_alloc_tsk_diff_prsv; eauto.
  + eapply taskcre_tcb_alloc_que_af_prsv; eauto.
  + eapply taskcre_tcb_alloc_que_dom_prsv; eauto.
  + eapply taskcre_tcb_alloc_mq_wt_prsv; eauto.
     constructor; eauto.
  + eapply taskcre_tcb_alloc_wt_mq_prsv; eauto.
    constructor; eauto.
  + eapply taskcre_tcb_alloc_chcfg_prsv; eauto.
  Qed.




Lemma dr_taskcre:
  forall vl t, 
    tl_vl_match (Tptr Tvoid :: Tptr Tvoid :: Tint8 :: nil) vl = true ->
    deduct_rules t (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (task_apispecs.taskcre vl) q_star. 
Proof.
  introv Htvm.
  eapply seq_rule with (q' := tcre_alloc_post vl).
  - (* tcre_tcb_alloc *)
    constructors.
    + apply stable_pre_trivial_asrt.
    + introv Hpre1 Halloc.
      split.
      unfolds. 
      splits.
      *
        eapply tcre_alloc_sat_post; eauto.
      *
        eapply taskcre_tcb_alloc_prsv_inv; eauto. 
      *
        eapply taskcre_tcb_alloc_guar; eauto.
      *
        splits.
        ** 
          eapply taskcre_tcb_alloc_sdom_iff; eauto.
        **
          introv Hac.
          eapply tcre_alloc_newtsk_same_dom; eauto.
        **
          (* integrity oblig. *)
          introv Hnex Hsd Hnfl.          
          eapply tcre_alloc_obsr_equiv_data; eauto.
    +
      (* confidentiality oblig. *)
      introv Hpre2 Halloc1 Halloc2 Hntck1 Hntck2.      
      des_pre2 Hpre2.
      unfolds in Halloc1.
      unfolds in Halloc2.
      do 7 (d_mt_hyp;
            try (simpl in Htvm; simpljoin; tryfalse; 
                 simpl in Halloc1; simpl in Halloc2;
                 inv_errp; inv_errp; simpljoin; splits; eauto; fail)
        ).
      d_if_hyp.
      * 
        simpl in Halloc1; simpl in Halloc2;
          inv_errp; inv_errp; simpljoin; splits; eauto.
      *
        subst. 
        destruct Halloc1 as (tls1 & pr_c1 & st_c1 & msg_c1 & sus_c1 & d_c1 & ts1 & Hgtls1 & Hgt1 & Hor1).
        destruct Halloc2 as (tls2 & pr_c2 & st_c2 & msg_c2 & sus_c2 & d_c2 & ts2 & Hgtls2 & Hgt2 & Hor2).

        lets H1_: tls_sdom_td_eq Hpre11 Hgtls1 Hgt1 Hsd1.
        lets H2_: tls_sdom_td_eq Hpre12 Hgtls2 Hgt2 Hsd2.
        subst d_c1 d_c2.

        pose proof (ex_tsk_or tls1 td' i) as Hor.
        destruct Hor as [Hext | Hnext].
        **
          destruct Hor1 as [Hex1 | Hnex1].
          ***
            destruct Hor2 as [Hex2 | Hnex2].
            {
              destruct Hex1; destruct Hex2.
              inv_errp; inv_errp; simpljoin; splits; eauto.
            }
            {
              lets Hf: ex_prio_12 Hdte' Hgtls1 Hgtls2 Hext.
              destruct Hnex2 as (Hnex2 & H'). 
              apply Hnex2 in Hf. false. 
            }
          ***
            destruct Hnex1 as (Hnex1 & H').
            apply Hnex1 in Hext.
            false. 
        **
          destruct Hor1 as [Hex1 | Hnex1].
          ***
            destruct Hex1 as (Hex1 & H').
            apply Hnext in Hex1. false.
          ***
            destruct Hnex1 as (_ & Hextsmp1).
            destruct Hor2 as [Hex2 | Hnex2].
            {
              destruct Hex2 as (Hex2 & H').
              lets H_: ex_prio_eqv i Hdte' Hgtls1 Hgtls2.
              rewrite H_ in Hnext.
              apply Hnext in Hex2.
              false.
            }
            {
              destruct Hnex2 as (_ & Hextsmp2).
              destruct Hextsmp1 as (tsmp1 & Hgtsmp1 & Hgts1 & Hmt1).
              destruct Hextsmp2 as (tsmp2 & Hgtsmp2 & Hgts2 & Hmt2).

              assert (ts1 = ts2).
              {
                eapply obsr_equiv_fts_eq; eauto.
              }
              subst ts1. rename ts2 into ts.
              destruct ts.
              - (* no free task *)
                inv_errp; inv_errp; simpljoin; splits; eauto.
              -
                simpljoin.
                splits; eauto.
                simpl.
                eapply tcre_alloc2_obser_equiv_tskd_prsv; eauto.
            }
        
  -
    introv Hinv Halp Hs2.
    unfolds in Halp.
    destruct Halp as [Hcont | Hncont].
    +
      destruct Hcont as (t_n & Hvl0).
      subst vl0.
      change (Int.eq Int.mone Int.mone) with true in Hs2.
      subst s2.

      split.
      * unfolds. simpl. unfolds; auto.
      * constructors.
        ** eapply dr_sched; eauto.
        ** introv Hi Hq_ Hs2.
           subst s2.
           split.
           *** apply ssp_end.
           *** constructors.
    +
      destruct Hncont as (i & Hneqi & Hvl0).
      subst vl0.
      rewrite Int.eq_false in Hs2; auto.
      subst s2.
      split.
      * apply ssp_end.
      * constructors.
Qed. 


  
