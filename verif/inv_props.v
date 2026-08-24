
Require Import LibTactics.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import state.
Require Import rules.
Require Import my_tacs.

Require Import specs_common. 
Require Import tick_spec.
Require Import sys_spec. 

Require Import aux_lemmas.

(* coarse-grained preservation of inv. *)  

Lemma same_tsks_ex_active_tsk:
  forall O O' t td, 
    get O abstcblsid = get O' abstcblsid -> 
    ex_active_tsk O t td ->
    ex_active_tsk O' t td. 
Proof.
  introv Hgeq Heat.
  unfold ex_active_tsk.
  unfold ex_active_tsk in Heat.
  destruct Heat as (tls & pr & st & msg & sus & Hgtls & Hgt).
  rewrite Hgeq in Hgtls.
  do 5 eexists; splits; eauto.
Qed. 
  
Lemma same_tsks_ex_free_tsk: 
  forall O O' t td, 
    get O freetid = get O' freetid -> 
    ex_free_tsk O t td ->
    ex_free_tsk O' t td. 
Proof.
  introv Hgeqf Heft.
  unfold ex_free_tsk.
  unfold ex_free_tsk in Heft.
  destruct Heft as (fts & ts & Hg' & Hgf & Hin).
  rewrite Hgeqf in Hg'.
  do 2 eexists; splits; eauto.
Qed.   

Lemma same_tsks_tsk_active_free_disj:
  forall O O', 
    get O abstcblsid = get O' abstcblsid -> 
    get O freetid = get O' freetid -> 
    tsk_active_free_disj O -> 
    tsk_active_free_disj O'. 
Proof.
  introv Hgeq Hgeqf Htafd.
  unfold tsk_active_free_disj in *.
  introv Heat Heft.
  assert (Heat_: ex_active_tsk O t td).
  {
    symmetry in Hgeq, Hgeqf.
    eapply same_tsks_ex_active_tsk; eauto.
  }
  assert (Heft_: ex_free_tsk O t td).
  {
    symmetry in Hgeq, Hgeqf.
    eapply same_tsks_ex_free_tsk; eauto.
  }
  eapply Htafd; eauto.
Qed.

Lemma same_tsks_sdom:
  forall O O' t td, 
    get O abstcblsid = get O' abstcblsid -> 
    get O freetid = get O' freetid ->
    sdom_ O t td ->
    sdom_ O' t td. 
Proof.
  introv Hgae Hgfe Hsd.
  unfold sdom_ in *.
  destruct Hsd as [Heat | Heft].
  - left.
    unfold ex_active_tsk in *.
    simpljoin.
    rewrite <- Hgae.
    do 5 eexists; splits; eauto.
  - right.
    unfold ex_free_tsk in *.
    simpljoin.
    rewrite <- Hgfe.
    do 2 eexists; splits; eauto.
Qed.     

Lemma same_tsks_tsk_dom_disj:
  forall O O', 
    get O abstcblsid = get O' abstcblsid -> 
    get O freetid = get O' freetid -> 
    tsk_dom_disj O ->
    tsk_dom_disj O'.
Proof.
  introv Hgeq Hgeqf Htdd.
  unfold tsk_dom_disj in *.
  introv Hsd1' Hsd2'.
  symmetry in Hgeq, Hgeqf.
  assert (Hsd1: sdom_ O t td1).
  {
    eapply same_tsks_sdom; eauto.
  }
  assert (Hsd2: sdom_ O t td2).
  {
    eapply same_tsks_sdom; eauto.
  }
  eapply Htdd; eauto.
Qed. 

Lemma same_tsks_tsk_diff_id_pr:
  forall O O', 
    get O abstcblsid = get O' abstcblsid -> 
    tsk_diff_id_prio O ->
    tsk_diff_id_prio O'.
Proof.
  introv Hgeq Htdip.
  unfold tsk_diff_id_prio in *.
  introv Hg' Hneq Hgt1 Hgt2.
  rewrite <- Hgeq in Hg'.
  specializes Htdip; eauto.
Qed. 

Lemma same_mqs_ex_active_que:
  forall O O' q td, 
    get O quelsid = get O' quelsid ->
    ex_active_que O q td ->
    ex_active_que O' q td.
Proof.
  introv Hgeq Heaq.
  unfold ex_active_que in *.
  rewrite <- Hgeq.
  auto.
Qed.   

Lemma same_mqs_ex_free_que:
  forall O O' q td, 
    get O freeqid = get O' freeqid -> 
    ex_free_que O q td -> 
    ex_free_que O' q td. 
Proof.
  introv Hgfeq Hefq.
  unfold ex_free_que in *.
  rewrite <- Hgfeq.
  auto.
Qed. 

Lemma same_mqs_que_active_free_disj:
  forall O O', 
    get O quelsid = get O' quelsid ->
    get O freeqid = get O' freeqid -> 
    que_active_free_disj O ->
    que_active_free_disj O'.  
Proof.
  introv Hgeq Hgeqf Hqaf.
  unfold que_active_free_disj in *.
  introv Heaq Hefq.
  symmetry in Hgeq, Hgeqf.
  eapply Hqaf; auto.
  eapply same_mqs_ex_active_que; eauto.
  eapply same_mqs_ex_free_que; eauto.
Qed.


Lemma same_mqs_que_dom_disj:
  forall O O', 
    get O quelsid = get O' quelsid ->
    get O freeqid = get O' freeqid ->   
    que_dom_disj O ->
    que_dom_disj O'.
Proof.
  introv Hgeq Hgeqf Hqdd.
  unfold que_dom_disj in *.
  introv Hqsd1' Hqsd2'.
  symmetry in Hgeq, Hgeqf.
  eapply Hqdd; eauto.
  all: eapply same_mqs_que_dom; eauto.
Qed. 

Lemma same_tsks_mqs_mq_wt_cond:
  forall O O', 
    get O abstcblsid = get O' abstcblsid ->
    get O quelsid = get O' quelsid ->
    mq_wt_cond O ->
    mq_wt_cond O'. 
Proof.
  introv Hgeq Hgeqq Hmwc.
  unfold mq_wt_cond in *.
  introv Hgqls' Hgtls' Hgq Hin.
  rewrite <- Hgeqq in Hgqls'.
  rewrite <- Hgeq in Hgtls'.
  eapply Hmwc; eauto.
Qed. 

Lemma same_tsks_mqs_wt_mq_cond:
  forall O O', 
    get O abstcblsid = get O' abstcblsid ->
    get O quelsid = get O' quelsid ->
    wt_mq_cond O ->
    wt_mq_cond O'. 
Proof.
  introv Hgeq Hgeqq Hwmc.
  unfold wt_mq_cond in *.
  introv Hgtls' Hgt Hgqls'.
  rewrite <- Hgeq in Hgtls'.
  rewrite <- Hgeqq in Hgqls'.
  eapply Hwmc; eauto.
Qed.   

Lemma same_chs_chs_sat_config:
  forall O O',     
    get O chlsid = get O' chlsid -> 
    chs_sat_config O ->
    chs_sat_config O'.
Proof.
  introv Hgeq Hcsc.
  unfold chs_sat_config in *.
  introv Hgchs' Hgc.
  rewrite <- Hgeq in Hgchs'.
  eapply Hcsc; eauto.
Qed.   
  
Lemma inv_coarse_prsv:
  forall O O', 
    I O -> 
    get O abstcblsid = get O' abstcblsid ->
    get O quelsid = get O' quelsid ->
    get O chlsid = get O' chlsid ->
    get O freetid = get O' freetid ->
    get O freeqid = get O' freeqid -> 
    I O'.
Proof.
  introv Hinv Hgeqt Hgeqq Hgeqc Hgeqft Hgeqfq.
  inverts Hinv.
  constructors.
  - eapply same_tsks_tsk_active_free_disj; eauto.
  - eapply same_tsks_tsk_dom_disj; eauto.
  - eapply same_tsks_tsk_diff_id_pr; eauto.
  - eapply same_mqs_que_active_free_disj; eauto.
  - eapply same_mqs_que_dom_disj; eauto.
  - eapply same_tsks_mqs_mq_wt_cond; eauto.
  - eapply same_tsks_mqs_wt_mq_cond; eauto.
  - eapply same_chs_chs_sat_config; eauto.
Qed. 


(* preservation of inv. under change of current task *) 

Lemma inv_ct_change_prsv: 
  forall (O : osabst) (cid : coreid) (td : task_dom) (t' : tid) (O' : osabst),
    I O ->
    cur_dom O cid td ->
    get_hprio_in_dom O td t' ->
    upd_cur_tsk O cid t' O' ->
    I O'. 
Proof.
  introv Hinv Hcd Hghpr Hupdct.
  inverts Hinv.
  unfold upd_cur_tsk in *.
  unfold state in Hupdct.
  unfolds in Hupdct.
  destruct Hupdct as (ct & ct' & Hgct & Hct' & HO').
  subst. 
  
  constructors.
  -
    eapply same_tsks_tsk_active_free_disj with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_tsks_tsk_dom_disj with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_tsks_tsk_diff_id_pr with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_mqs_que_active_free_disj with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_mqs_que_dom_disj with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_tsks_mqs_mq_wt_cond with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_tsks_mqs_wt_mq_cond with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    eapply same_chs_chs_sat_config with (O:=O); eauto.
    all: rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
Qed. 


(* preservation of inv. under ticks *)  

Lemma tickchange_active_free_disj:
  forall t st tls tls' qls st' qls' p msg sus td O, 
    tickchange t st qls st' qls' -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' -> 
    tsk_active_free_disj O -> 
    tsk_active_free_disj
      (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  intros t st tls tls' qls st' qls' p msg sus td O Htick Hget Hgtls Htls Hdisj.
  unfold tsk_active_free_disj in *.
  intros t' td'.
  introv Hact Hfree.
  assert (ex_active_tsk O t' td').
  {
    unfold ex_active_tsk in Hact.
    destruct Hact as (tls0 & pr0 & st0 & msg0 & sus0 & Hcb & Hget_).
    rewrite neq_set_get in Hcb; eauto. 2: introv Hf; inverts Hf.
    rewrite map_get_set in Hcb.
    inverts Hcb.
    casetac t t' He Hne.
    - subst.
      rewrite map_get_set in Hget_.
      inverts Hget_.
      unfolds.
      do 5 eexists; splits; eauto.
    - rewrite <- H in Hget_.
      rewrite neq_set_get in Hget_; eauto.
      unfolds.
      do 5 eexists; splits; eauto.
  }
  assert (ex_free_tsk O t' td').
  {
    unfold ex_free_tsk in Hfree. 
    destruct Hfree as (fts & ts & Hft & Hfts & Hin).
    rewrite neq_set_get in Hft; eauto.
    2: introv Hf; inverts Hf.
    rewrite neq_set_get in Hft; eauto.
    2: introv Hf; inverts Hf.
    unfolds.
    do 2 eexists; splits; eauto.
  }
  eapply Hdisj; eauto.
Qed. 

Lemma ex_active_task_rev:
  forall O tls tls' qls' p st st' msg sus t t0 td td', 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' ->       
    ex_active_tsk (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) t0 td' ->
    ex_active_tsk O t0 td'. 
Proof.
  introv Hgtls Hgt Htls' Heat.
  unfold ex_active_tsk in *.
  destruct Heat as (tls0 & pr0 & st0 & msg0 & sus0 & Habs & Hget).
  rewrite neq_set_get in Habs; eauto.
  2: intro Hf; inverts Hf.
  rewrite map_get_set in Habs.
  inverts Habs.
  rewrite <- H in Hget.
  casetac t t0 He Hne.
  - subst. rewrite map_get_set in Hget.
    inverts Hget.
    do 5 eexists; splits; eauto.
  - rewrite neq_set_get in Hget; eauto.
    do 5 eexists; splits; eauto.
Qed.

Lemma ex_free_task_rev:
  forall O tls tls' qls' p st st' msg sus t t0 td td', 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' ->       
    ex_free_tsk (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) t0 td' ->
    ex_free_tsk O t0 td'. 
Proof.
  introv Hgtls Hgt Htls' Heft.
  unfold ex_free_tsk in *.
  destruct Heft as (fts & ts & Hft & Hfts & Hin).
  rewrite neq_set_get in Hft; eauto.
  2: { introv Hf; inverts Hf. }
  rewrite neq_set_get in Hft; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma tickchange_tsk_dom_disj:
  forall t st tls tls' qls st' qls' p msg sus td O, 
    tickchange t st qls st' qls' -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' -> 
    tsk_dom_disj O -> 
    tsk_dom_disj (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  introv Htck Hgtls Hgt Hset Htdd.
  unfold tsk_dom_disj in *.
  introv Hsd1 Hsd2.
  unfold sdom_ in *.
  destruct Hsd1 as [Heat1 | Heft1].
  -
    assert (Heat01: ex_active_tsk O t0 td1).
    {
      eapply ex_active_task_rev; eauto.
    }
    destruct Hsd2 as [Heat2 | Heft2].
    + 
      assert (Heat02: ex_active_tsk O t0 td2).
      {
        eapply ex_active_task_rev; eauto.
      }
      eapply Htdd; eauto.
    +
      assert (Heft02: ex_free_tsk O t0 td2).
      {
        eapply ex_free_task_rev; eauto.
      }
      eapply Htdd; eauto.
  -
    assert (Heft01: ex_free_tsk O t0 td1).
    {
      eapply ex_free_task_rev; eauto.
    }
    destruct Hsd2 as [Heat2 | Heft2].
    + 
      assert (Heat02: ex_active_tsk O t0 td2).
      {
        eapply ex_active_task_rev; eauto.
      }
      eapply Htdd; eauto.
    +
      assert (Heft02: ex_free_tsk O t0 td2).
      {
        eapply ex_free_task_rev; eauto.
      }
      eapply Htdd; eauto.
Qed.

Lemma tls_set_tsk_diff_idpr: 
  forall O tls t p st msg sus td st' tls' qls',
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' -> 
    tsk_diff_id_prio O -> 
    tsk_diff_id_prio (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  introv Htls Ht Hset Htdip.
  unfold tsk_diff_id_prio in *.
  rewrite neq_set_get; eauto.
  2: introv Hf; inverts Hf.
  rewrite map_get_set.
  introv Heq Hneq Hg1 Hg2.
  inverts Heq.
  subst tls0.
  casetac t t1 He1 Hne1.
  - subst. rewrite map_get_set in Hg1.
    inverts Hg1.
    rewrite neq_set_get in Hg2; eauto.
  - rewrite neq_set_get in Hg1; eauto.
    casetac t t2 He2 Hne2.
    +
      subst.
      rewrite map_get_set in Hg2. inverts Hg2.
      eauto.
    +
      rewrite neq_set_get in Hg2; eauto.
Qed.    

Lemma tickchange_inversion: 
  forall t st qls st' qls', 
    tickchange t st qls st' qls' -> 
    (qls' = qls \/
       exists qid0 d ms sz ts,
         st = wait (os_stat_qpend qid0) (Some Int.one) /\
           get qls qid0 = Some (msgq ms sz ts, d) /\
           qls' = set qls qid0 (msgq ms sz (remove_tid t ts), d)). 
Proof.
  introv Htch.
  inverts Htch.
  - left; auto.
  - left; auto.
  - right.
    do 5 eexists; splits; eauto.
Qed. 

Lemma tickchange_que_active_free_disj:
  forall O qls qls' t st st' tls', 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' -> 
    que_active_free_disj O -> 
    que_active_free_disj
      (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  introv Hgq Htch Hqaf.
  lets Hor: tickchange_inversion Htch.
  destruct Hor as [Heq | Hupd].
  - subst.
    unfold que_active_free_disj in *.
    introv Hexa Hexf.
    assert (Hexa0: ex_active_que O q td).
    {
      unfold ex_active_que in Hexa.
      rewrite map_get_set in Hexa.
      destruct Hexa as (qls0 & ms & sz & ts & Heq & Hgq_).
      inverts Heq. 
      unfolds.
      do 4 eexists; splits; eauto.
    }
    assert (Hexf0: ex_free_que O q td).
    {
      unfold ex_free_que in Hexf.
      rewrite neq_set_get in Hexf; eauto.
      2: introv Hf; inverts Hf.
      rewrite neq_set_get in Hexf; eauto.
      introv Hf; inverts Hf.
    }
    eapply Hqaf; eauto.
  -
    unfold que_active_free_disj in *.
    destruct Hupd as (qid0 & d & ms & sz & ts & Hst & Hget & Hqls').
    introv Hexa Hexf.
    subst.
    assert (Hexa0: ex_active_que O q td).
    {
      unfold ex_active_que in Hexa.
      unfolds.
      rewrite map_get_set in Hexa.
      destruct Hexa as (qls0 & ms0 & sz0 & ts0 & Heqs & Hgetq).
      inverts Heqs.
      casetac qid0 q He Hf.
      - subst.
        rewrite map_get_set in Hgetq.
        inverts Hgetq.
        do 4 eexists; splits; eauto.
      - rewrite neq_set_get in Hgetq; eauto.
        do 4 eexists; splits; eauto.
    }
    assert (Hexf0: ex_free_que O q td).
    {
      unfold ex_free_que in Hexf.
      unfolds.
      rewrite neq_set_get in Hexf; eauto.
      2: introv Hf; inverts Hf.
      
      destruct Hexf as (fqs & qs & Hgf & Hgs & Hin).
      rewrite neq_set_get in Hgf; eauto.
      introv Hf; inverts Hf.
    }
    eapply Hqaf; eauto.
Qed.

Lemma tickch_ex_active_que_rev: 
  forall t st st' tls' qls qls' td q O, 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' -> 
    ex_active_que
      (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) q td -> 
    ex_active_que O q td. 
Proof.
  introv Hgqls Htch Heaq.
  unfold ex_active_que in *.
  destruct Heaq as (qls_ & ms & sz & ts & Hgqls_ & Hgq).
  rewrite map_get_set in Hgqls_.
  inverts Hgqls_.
  lets H__: tickchange_inversion Htch.
  destruct H__ as [Heq | Hupd].
  - 
    subst. do 4 eexists; splits; eauto.
  -
    destruct Hupd as (qid0 & d & ms_ & sz_ & ts_ & Hst & Hget & Hqls').
    subst qls_.
    casetac qid0 q He Hne.
    + subst.
      rewrite map_get_set in Hgq.
      inverts Hgq.
      do 4 eexists; splits; eauto.
    + rewrite neq_set_get in Hgq; eauto.
      subst.
      do 4 eexists; splits; eauto.
Qed. 

Lemma tickch_ex_free_que_rev: 
  forall t st st' tls' qls qls' td q O, 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' -> 
    ex_free_que
      (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) q td -> 
    ex_free_que O q td. 
Proof.
  introv Hgqls Htch Hefq.
  unfold ex_free_que in *.
  destruct Hefq as (fqs & qs & Hgf & Hgq & Hin).
  rewrite neq_set_get in Hgf; eauto.
  2: { introv Hf; inverts Hf. }
  rewrite neq_set_get in Hgf; eauto.
  introv Hf; inverts Hf. 
Qed.       

Lemma tickchange_q_dom_disj:
  forall O qls t st st' qls' tls', 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' -> 
    que_dom_disj O -> 
    que_dom_disj (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  introv Hgqls Htch Hqd.
  unfold que_dom_disj in *.
  introv Hqd1 Htd2.
  unfold q_sdom_ in *.
  destruct Hqd1 as [Heaq1 | Hefq1].
  -
    assert (ex_active_que O q td1).
    {
      eapply tickch_ex_active_que_rev; eauto.
    }
    +
      destruct Htd2 as [Heaq2 | Hefq2].
      *
        assert (ex_active_que O q td2).
        {
          eapply tickch_ex_active_que_rev; eauto.
        }
        eapply Hqd; eauto.
      *
        assert (ex_free_que O q td2).
        {
          eapply tickch_ex_free_que_rev; eauto.
        }          
        eapply Hqd; eauto.
  -
    assert (ex_free_que O q td1).
    {
      eapply tickch_ex_free_que_rev; eauto.
    }
    +
      destruct Htd2 as [Heaq2 | Hefq2].
      *
        assert (ex_active_que O q td2).
        {
          eapply tickch_ex_active_que_rev; eauto.
        }
        eapply Hqd; eauto.
      *
        assert (ex_free_que O q td2).
        {
          eapply tickch_ex_free_que_rev; eauto.
        }          
        eapply Hqd; eauto.
Qed.           

Lemma tickchange_mq_wt_cond:
  forall O tls t p st msg sus td qls st' qls' tls', 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' -> 
    set tls t (p, st', msg, sus, td) = tls' -> 
    mq_wt_cond O -> 
    mq_wt_cond (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  introv Hgtls Hgt Hgqls Htch Hset Hmqc.
  unfold mq_wt_cond in *.
  introv Hgetq Hgett Hgq Hin.
  rewrite map_get_set in Hgetq.
  rewrite neq_set_get in Hgett; eauto.
  2: { introv Hf; inverts Hf. }
  rewrite map_get_set in Hgett.
  inverts Hgetq.
  inverts Hgett.
  inverts Htch.
  - 
    lets H_: Hmqc Hgqls Hgtls Hgq Hin.
    destruct H_ as (pr & msg0 & sus_ & to & Hgtt).
    casetac t0 t He Hne.
    + subst.
      rewrite Hgt in Hgtt.
      inverts Hgtt.
      rewrite map_get_set.
      do 4 eexists; eauto.
    + 
      subst tls0.
      rewrite neq_set_get; eauto.
  -
    lets H_: Hmqc Hgqls Hgtls Hgq Hin.
    destruct H_ as (pr & msg0 & sus_ & to & Hgtt).
    subst tls0.
    casetac t0 t He Hne.
    + subst.
      rewrite map_get_set.
      rewrite Hgt in Hgtt.
      inverts Hgtt.
      lets H_: Hmqc Hgqls Hgtls Hgq Hin.
      destruct H_ as (pr_ & msg_ & sus & to_ & H_).
      rewrite Hgt in H_.
      inverts H_.
      do 4 eexists; eauto.
    +
      rewrite neq_set_get; eauto.
  -
    casetac qid q He Hne.
    + subst. rewrite map_get_set in Hgq.
      inverts Hgq.
      casetac t t0 He Hne.
      * subst.
        apply in_remove_tid_false in Hin; false.
      * rewrite neq_set_get.
        2: { apply not_eq_sym; auto. }
        eapply Hmqc; eauto.
        eapply in_remove_tid; eauto.
    + rewrite neq_set_get in Hgq.
      2: { apply not_eq_sym; auto. }
      subst tls0.
      lets H_: Hmqc Hgqls Hgtls Hgq Hin.
      destruct H_ as (pr & msg0 & sus_ & to & Hgt').
      casetac t t0 He_ Hne_.
      * subst.
        rewrite Hgt' in Hgt.
        inverts Hgt.
        false.
      * rewrite neq_set_get; eauto.
Qed. 

Lemma tickchange_wt_mq_cond:
  forall O tls t p st msg sus td qls st' qls' tls', 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' -> 
    set tls t (p, st', msg, sus, td) = tls' -> 
    wt_mq_cond O -> 
    wt_mq_cond (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')). 
Proof.
  introv Hgtls Hgt Hgqls Htch Hset Hwmc.
  unfold wt_mq_cond in *.
  rewrite neq_set_get; eauto.
  2: introv Hf; inverts Hf.
  repeat rewrite map_get_set.
  introv Heqs Hgt0 Heqsq.
  inverts Heqs; inverts Heqsq.
  subst tls0.
  inverts Htch.
  - 
    casetac t t0 He Hne.
    + subst.
      inverts Hgt0.
      rewrite map_get_set in H1.
      inverts H1.      
      lets H_: Hwmc Hgtls Hgt Hgqls.
      auto.
    + rewrite neq_set_get in Hgt0; eauto.
  -
    casetac t t0 He Hne.
    + subst.
      rewrite map_get_set in Hgt0.
      inverts Hgt0.
      lets H_: Hwmc Hgtls Hgt Hgqls.
      auto.
    + rewrite neq_set_get in Hgt0; eauto.
  -
    casetac t t0 He Hne.
    + subst.
      rewrite map_get_set in Hgt0.
      inverts Hgt0.
    + rewrite neq_set_get in Hgt0; eauto.
      casetac q qid He_ Hne_.
      * subst.
        lets H_: Hwmc Hgtls Hgt0 Hgqls.
        rewrite map_get_set.
        destruct H_ as (ms_ & sz_ & ts_ & Hgq & Hin).
        rewrite Hgq in H0. inverts H0.
        do 3 eexists; splits; eauto.
        eapply in_remove_tid'; eauto.
      * rewrite neq_set_get; eauto.
Qed.         

Lemma chseq_chs_sat_cfg_prsv:
  forall O O', 
    chs_sat_config O -> 
    get O chlsid = get O' chlsid ->
    chs_sat_config O'.
Proof.
  introv Hcc Heq.
  unfold chs_sat_config in *.
  introv Hgchs Hgc.
  rewrite <- Heq in Hgchs.
  lets H__: Hcc Hgchs Hgc.
  clear Hcc.
  auto.
Qed. 

Lemma tickchange_prsv_inv: 
  forall t st qls qls' st' (tls tls': TcbMod.map) p msg sus td O,
    I O -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' ->     
    set tls t (p, st', msg, sus, td) = tls' ->
    I (set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')).
Proof.
  introv Hinv Hgtls Hgt Hgqls Htchg Hset.
  inverts Hinv.
  constructors.
  -
    eapply tickchange_active_free_disj; eauto.
  -
    eapply tickchange_tsk_dom_disj; eauto.
  -
    eapply tls_set_tsk_diff_idpr; eauto.
  -
    eapply tickchange_que_active_free_disj; eauto.
  -
    eapply tickchange_q_dom_disj; eauto.
  -
    eapply tickchange_mq_wt_cond; eauto.
  -
    eapply tickchange_wt_mq_cond; eauto.
  -
    eapply chseq_chs_sat_cfg_prsv; eauto.
    rewrite neq_set_get; eauto.
    2: { introv Hf; inverts Hf. }
    rewrite neq_set_get; eauto.
    introv Hf; inverts Hf.
  (* - *)
  (*   eapply scheq_dsch_data_valid_prsv; eauto;  *)
  (*   repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)). *)
Qed. 
