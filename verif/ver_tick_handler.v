
Require Import LibTactics.
Require Import join_lib.
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import rules. 

Require Import specs_common.
Require Import state.
Require Import my_tacs.

Require Import tick_spec. 
Require Import sys_spec.

Require Import rly_guar.
Require Import flow_policy.
Require Import obsr_equiv. 

Require Import aux_lemmas.
Require Import inv_props. 

Lemma tickchange_prsv_inv: 
  forall t st qls qls' st' (tls tls': TcbMod.map) p msg sus td O O',
    I O -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' ->     
    set tls t (p, st', msg, sus, td) = tls' ->
    get O' abstcblsid = Some (abstcblist tls') ->
    get O' quelsid = Some (absecblist qls') -> 
    get O' chlsid = get O chlsid -> 
    get O' freetid = get O freetid ->
    get O' freeqid = get O freeqid -> 
    I O'. 
Proof.
  introv Hinv Hgtls Hgt Hgqls Htc Htls' Hgtls' Hgqls' Heq.
  introv Heqft Heqfq.
  lets H__: tickchange_prsv_inv Hinv Hgtls Hgt Hgqls Htc Htls'.
  eapply inv_coarse_prsv with
    (O:=(set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls'))); eauto.
  -
    rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
    rewrite map_get_set.
    symmetry; auto.
  -
    rewrite map_get_set.
    symmetry; auto.
  -
    repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
  -
    repeat rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
Qed. 

Lemma tickstep_prsv_inv: 
  forall (tls tls' tls_: TcbMod.map) qls qls' td,
    tickstep' td tls qls tls' qls' tls_ ->
    Maps.sub tls_ tls -> 
    forall O O', 
    I O -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get O quelsid = Some (absecblist qls) -> 
    get O' abstcblsid = Some (abstcblist tls') ->
    get O' quelsid = Some (absecblist qls') -> 
    get O' chlsid = get O chlsid -> 
    get O' freetid = get O freetid ->
    get O' freeqid = get O freeqid -> 
    I O'. 
Proof.
  introv Hts.
  induction Hts;
    introv Hsub Hinv Hgtls Hgqls Hgtls' Hgqls' Hceq Hfteq Hfqeq.
  
  - eapply inv_coarse_prsv with (O:=O); eauto.
    all: congruence.
    
  - set (O'_ := set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')).
    eapply IHHts with (O:=O'_); eauto.
    {
      eapply sub_join_set_sub; eauto.
    }
    { (* I O'_ *) 
      assert (Hgu: get tls_used t = Some (p, st, msg0, sus0, td)).
      { jeat. }
      assert (Hgt_: get tls t = Some (p, st, msg0, sus0, td)).
      { clear -Hsub Hgu. unfolds in Hsub. simpljoin. jeat. }

      lets H_: tickchange_prsv_inv Hinv Hgtls Hgt_ Hgqls H0 H1. 
      eapply H_; auto. clear H_.
      all: subst O'_.
      - rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
        rewrite map_get_set.
        auto.
      - rewrite map_get_set.
        auto.
      - repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      - repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      - repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
    all: subst O'_.
    {
      rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
      rewrite map_get_set.
      auto.
    }
    {
      rewrite map_get_set.
      auto.
    }
    {
      repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
    {
      repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
    {
      repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
    
  -
    eapply IHHts; eauto.
    assert (Maps.sub tls_used' tls_used).
    {
      unfolds in H.
      unfolds. eexists; jeat.
    }
    eapply sub_trans; eauto.
Qed. 

Lemma tickisr_spec_inv_prsv:
  forall O vl' O' t ac
         (Hinv : I O)
         (Htckspc : tickisr_spec t nil O ac (vl', O')), 
    I O'. 
Proof.
  intros. 
  unfolds in Htckspc.
  destruct Htckspc as (tls & qls & ctid & dtmp & dt & cdmp & cd & cid_ & Hgct &
                         Hgt & Hgtls & Hgqls & Hgdtmp & Hgdt & Hact & Hgcmp & Hgcd & Hex).
  
  destruct Hex as (tls' & qls' & Hstep & Hif).
  subst ac.
  
  d_if_hyp.
  
  - (* case where current domain changes *)

    destruct Hif as (imp & lmp & ldmp & scdmp & idx & len & ld & schd & H'). 
    destruct H' as (Hgimp & Hgidx & Hglmp & Hglen & Hgldmp &
                      Hgld & Hgscdmp & Hgschd & H'). 
    
    d_mt_hyp.
    *
      destruct p. 
      destruct H' as (HO' & Hvl').
      subst.
      eapply tickstep_prsv_inv with (O:=O); eauto.
      { apply sub_refl. }
      {
        do 5 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        auto.
      }
      {
        do 4 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        auto.
      }
      {
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      }
      {
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      }
      {
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      }
    *          
      simpljoin; auto.
      
  - (* case where current domain does not change *)

    simpljoin; subst.
    eapply tickstep_prsv_inv with (O:=O); eauto.
    { apply sub_refl. }
    {
      do 2 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      rewrite map_get_set; auto.
    }
    {
      rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
      rewrite map_get_set; auto.
    }
    all: repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
Qed. 

Lemma tickchange_ex_active_tsk_prsv0:
  forall O t tls p st msg sus td st' tls' (* qls qls' *) O', 
    ex_active_tsk O t td -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    (* tickchange t st qls st' qls' ->      *)
    set tls t (p, st', msg, sus, td) = tls' ->
    get O' abstcblsid = Some (abstcblist tls') ->
    ex_active_tsk O' t td. 
Proof.
  introv Heat Hgtls Hgt (* Htc *) Htls' Hgtls'.
  unfold ex_active_tsk in *.
  destruct Heat as (tls_ & pr & st_ & msg_ & sus_ & Hgtls_ & Hgt_).
  rewrite Hgtls in Hgtls_; symmetry in Hgtls_; inverts Hgtls_.
  rewrite Hgt in Hgt_; symmetry in Hgt_; inverts Hgt_.
  rewrite Hgtls'.
  rewrite <- Htls'.
  do 5 eexists; splits; eauto.
  rewrite map_get_set; eauto.
Qed.

Lemma tickchange_ex_active_tsk_prsv:
  forall O t t' tls p st msg sus td st' tls' (* qls qls' *) O' td', 
    ex_active_tsk O t' td' -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' ->
    get O' abstcblsid = Some (abstcblist tls') ->
    ex_active_tsk O' t' td'. 
Proof.
  introv Heat Hgtls Hgt Htls' Hgtls'.
  unfold ex_active_tsk in *.
  destruct Heat as (tls_ & pr & st_ & msg_ & sus_ & Hgtls_ & Hgt_).
  rewrite Hgtls in Hgtls_; symmetry in Hgtls_; inverts Hgtls_.
  casetac t t' He Hne.
  - subst. 
    rewrite Hgt in Hgt_; symmetry in Hgt_; inverts Hgt_.
    rewrite Hgtls'.
    do 5 eexists; splits; eauto.
    rewrite map_get_set; eauto.
  - rewrite Hgtls'.
    do 5 eexists; splits; eauto.
    subst tls'.
    rewrite neq_set_get; eauto.
Qed.     

Lemma tickchange_sdom_prsv:
  forall O t t' tls p st msg sus td st' tls' (* qls qls' *) O' td', 
    sdom_ O t' td' ->
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' ->
    get O' abstcblsid = Some (abstcblist tls') ->
    get O' freetid = get O freetid -> 
    sdom_ O' t' td'.
Proof.
  introv Hsd Hgtls Hgt Htls' Hgtls' Hgeq.
  destruct Hsd as [Heat | Heft].
  - left.
    eapply tickchange_ex_active_tsk_prsv; eauto.
  - right.
    unfold ex_free_tsk in *.
    rewrite Hgeq. auto.
Qed.     
    
Lemma tickstep_prsv_sdom_: 
  forall (tls tls' tls_: TcbMod.map) qls qls' td td',
    tickstep' td tls qls tls' qls' tls_ ->
    Maps.sub tls_ tls -> 
    forall O O' t, 
      sdom_ O t td' -> 
      get O abstcblsid = Some (abstcblist tls) -> 
      get O' abstcblsid = Some (abstcblist tls') ->
      get O' freetid = get O freetid ->
      sdom_ O' t td'.
Proof.
  introv Hts.
  induction Hts; introv Hsub Hsd Hgtls Hgtls' Hgeqf.
  
  - assert (Hgeqt: get O abstcblsid = get O' abstcblsid) by congruence. 
    unfold sdom_ in *.
    destruct Hsd as [Heat | Heft].
    + unfold ex_active_tsk in *.
      rewrite <- Hgeqt.
      auto.
    + right.
      unfold ex_free_tsk in *.
      rewrite Hgeqf.
      auto.
      
  - set (O'_ := set O abstcblsid (abstcblist tls')).
    assert (Hgu: get tls_used t = Some (p, st, msg0, sus0, td)).
    {
      unfolds in H. jeat.
    }
    assert (Hgt: get tls t = Some (p, st, msg0, sus0, td)).
    {
      unfolds in Hsub.
      simpljoin. jeat.
    }
      
    assert (Hsd_: sdom_ O'_ t0 td').
    {
      lets H_: tickchange_sdom_prsv t t0 Hsd Hgtls Hgt H1; eauto.
      eapply H_; eauto.
      subst O'_.
      rewrite map_get_set. auto.
      subst O'_.
      rewrite neq_set_get; eauto.
      introv Hf; inverts Hf.
    }

    assert (Hsub': Maps.sub tls_used' tls').
    {
      eapply sub_join_set_sub; eauto.
    }
    lets H_: IHHts Hsub' Hsd_.
    eapply H_; eauto.
    all: subst O'_.
    rewrite map_get_set.
    auto.
    rewrite neq_set_get; eauto.
    introv Hf; inverts Hf.
    
  -
    assert (Hsub_: Maps.sub tls_used' tls_used).
    {
      unfolds in H.
      unfolds.
      eexists. jeat.
    }
    assert (Hsub': Maps.sub tls_used' tls).
    {
      eapply sub_trans; eauto.
    }
    specialize (IHHts Hsub').
    eapply IHHts; eauto.
Qed. 
    
Lemma tickisr_spec_sdom_prsv:
  forall t t' O ac vl' O' td
         (Htckspc : tickisr_spec t nil O ac (vl', O'))
         (Hsd : sdom_ O t' td), 
    sdom_ O' t' td. 
Proof.
  intros.
  unfolds in Htckspc.
  destruct Htckspc as (tls & qls & ctid & dtmp & dt & cdmp & cd & cid_ & Hgct &
                         Hgt & Hgtls & Hgqls & Hgdtmp & Hgdt & Hact & Hgcmp & Hgcd & Hex).
  
  destruct Hex as (tls' & qls' & Hstep & Hif).
  subst ac.
  
  d_if_hyp.
  
  - (* case where current domain changes *)

    destruct Hif as (imp & lmp & ldmp & scdmp & idx & len & ld & schd & H'). 
    destruct H' as (Hgimp & Hgidx & Hglmp & Hglen & Hgldmp &
                      Hgld & Hgscdmp & Hgschd & H'). 
    
    d_mt_hyp.
    *
      destruct p. 
      unfolds in Hstep.
      destruct H'; subst O'.
      eapply tickstep_prsv_sdom_ with (O:=O); eauto.
      { apply sub_refl. }
      {
        do 5 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        auto.
      }
      {
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      }
    *
      destruct H'.
      subst.
      auto.
  -
    destruct Hif.
    subst O'.
    eapply tickstep_prsv_sdom_ with (O:=O); eauto.
    { apply sub_refl. }
    {
      do 2 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      rewrite map_get_set.
      auto.
    }
    {
      repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
Qed.

Lemma tickchange_ex_active_que_prsv:
  forall O t st td st' qls qls' O' q, 
    ex_active_que O q td -> 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' ->
    get O' quelsid = Some (absecblist qls') -> 
    ex_active_que O' q td.
Proof.
  introv Heaq Hqls Htc Hg'.
  unfold ex_active_que in *.
  lets H__: tickchange_inversion Htc.
  rewrite Hg'.
  destruct Heaq as (qls_ & ms_ & sz_ & ts_ & Hgqls_ & Hgq_).
  rewrite Hqls in Hgqls_; symmetry in Hgqls_; inverts Hgqls_. 
  destruct H__ as [Heq | Hupd].
  - subst.
    do 4 eexists; splits; eauto.
  - destruct Hupd as (qid0 & d & ms & sz & ts & Hst & Hgq0 & Hqls').
    subst.
    casetac q qid0 He Hne.
    +
      subst.
      rewrite Hgq0 in Hgq_; symmetry in Hgq_; inverts Hgq_.
      do 4 eexists; splits; eauto.
      rewrite map_get_set; eauto.
    +
      do 4 eexists; splits; eauto.
      rewrite neq_set_get; eauto.
Qed.

Lemma tickchange_q_sdom_prsv:
  forall O t st td st' qls qls' O' q, 
    q_sdom_ O q td -> 
    get O quelsid = Some (absecblist qls) -> 
    tickchange t st qls st' qls' ->
    get O' quelsid = Some (absecblist qls') -> 
    get O' freeqid = get O freeqid -> 
    q_sdom_ O' q td. 
Proof.
  introv Hqsd Hgqls Htc Hgqls' Hgfq.
  unfold q_sdom_ in *.
  destruct Hqsd as [Heaq | Hefq].
  - left.
    eapply tickchange_ex_active_que_prsv; eauto.
  - right.
    unfold ex_free_que in *.
    rewrite Hgfq.
    auto.
Qed.     
               
Lemma tickstep_prsv_q_sdom_: 
  forall (tls tls' tls_: TcbMod.map) qls qls' td td',
    tickstep' td tls qls tls' qls' tls_ ->
    Maps.sub tls_ tls -> 
    forall O O' t, 
      q_sdom_ O t td' -> 
      (* get O abstcblsid = Some (abstcblist tls) ->  *)
      (* get O' abstcblsid = Some (abstcblist tls') -> *)
      get O quelsid = Some (absecblist qls) ->
      get O' quelsid = Some (absecblist qls') -> 
      get O' freeqid = get O freeqid ->
      q_sdom_ O' t td'.
Proof.
  introv Hts.
  induction Hts; introv Hsub Hqsd Hgqls Hgqls' Hgfq.

  - eapply same_mqs_que_dom with (O:=O); eauto.
    congruence.

  -
    set (O'_ := set O quelsid (absecblist qls')).
    assert (Hqsd_: q_sdom_ O'_ t0 td').
    {
      lets H__: tickchange_q_sdom_prsv Hqsd Hgqls H0.
      eapply H__; eauto.
      all: subst O'_. 
      {
        rewrite map_get_set. auto.
      }
      {
        rewrite neq_set_get; eauto.
        introv Hf; inverts Hf.
      }
    }
    assert (Hsub_: Maps.sub tls_used' tls').
    {
      eapply sub_join_set_sub; eauto.
    }
    specialize (IHHts Hsub_).
    eapply IHHts; eauto.
    all: subst O'_.
    {
      rewrite map_get_set; auto.
    }
    {
      rewrite neq_set_get; eauto.
      introv Hf; inverts Hf.
    }
    
  -
    assert (Hsub_: Maps.sub tls_used' tls_used).
    {
      unfolds in H.
      unfolds.
      eexists. jeat.
    }
    assert (Hsub': Maps.sub tls_used' tls).
    {
      eapply sub_trans; eauto.
    }
    specialize (IHHts Hsub').
    eapply IHHts; eauto.
Qed. 

Lemma tickisr_spec_q_sdom_prsv:
  forall t O ac vl' O' td q
         (Htckspc : tickisr_spec t nil O ac (vl', O'))
         (Hqsd : q_sdom_ O q td), 
    q_sdom_ O' q td.   
Proof.
  intros.
  unfolds in Htckspc.
  destruct Htckspc as (tls & qls & ctid & dtmp & dt & cdmp & cd & cid_ & Hgct &
                         Hgt & Hgtls & Hgqls & Hgdtmp & Hgdt & Hact & Hgcmp & Hgcd & Hex).
  
  destruct Hex as (tls' & qls' & Hstep & Hif).
  subst ac.
  
  d_if_hyp.
  
  - (* case where current domain changes *)

    destruct Hif as (imp & lmp & ldmp & scdmp & idx & len & ld & schd & H'). 
    destruct H' as (Hgimp & Hgidx & Hglmp & Hglen & Hgldmp &
                      Hgld & Hgscdmp & Hgschd & H'). 
    
    d_mt_hyp.
    *
      destruct p. 
      unfolds in Hstep.
      destruct H'; subst O'.
      eapply tickstep_prsv_q_sdom_ with (O:=O); eauto.
      { apply sub_refl. }
      {
        do 4 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        auto.
      }
      {
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      }
    *
      destruct H'.
      subst.
      auto.
  -
    destruct Hif.
    subst O'.
    eapply tickstep_prsv_q_sdom_ with (O:=O); eauto.
    { apply sub_refl. }
    {
      rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).
      rewrite map_get_set.
      auto.
    }
    {
      repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
Qed.   

Lemma tickchange_ex_active_tsk_prsv_rev:
  forall O t t' tls p st msg sus td st' tls' (* qls qls' *) O' td', 
    ex_active_tsk O' t' td' -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' ->
    get O' abstcblsid = Some (abstcblist tls') ->
    ex_active_tsk O t' td'. 
Proof.
  introv Heat Hgtls Hgt Htls' Hgtls'.
  unfold ex_active_tsk in *.
  destruct Heat as (tls_ & pr & st_ & msg_ & sus_ & Hgtls_ & Hgt_).
  rewrite Hgtls' in Hgtls_; symmetry in Hgtls_; inverts Hgtls_.
  casetac t t' He Hne.
  - subst.
    rewrite map_get_set in Hgt_. inverts Hgt_.
    rewrite Hgtls.
    do 5 eexists; splits; eauto.
  - subst tls'.
    rewrite neq_set_get in Hgt_; eauto.
    rewrite Hgtls.
    do 5 eexists; splits; eauto.
Qed.

Lemma tickchange_sdom_prsv_rev:
  forall O t t' tls p st msg sus td st' tls' (* qls qls' *) O' td', 
    sdom_ O' t' td' ->
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some (p, st, msg, sus, td) -> 
    set tls t (p, st', msg, sus, td) = tls' ->
    get O' abstcblsid = Some (abstcblist tls') ->
    get O' freetid = get O freetid -> 
    sdom_ O t' td'.
Proof.
  introv Hsd Hgtls Hgt Htls' Hgtls' Hgeq.
  destruct Hsd as [Heat | Heft].
  - left. 
    eapply tickchange_ex_active_tsk_prsv_rev; eauto.
  - right.
    unfold ex_free_tsk in *.
    rewrite <- Hgeq. auto.
Qed.     

Lemma tickstep_prsv_sdom_rev: 
  forall (tls tls' tls_: TcbMod.map) qls qls' td td',
    tickstep' td tls qls tls' qls' tls_ ->
    Maps.sub tls_ tls -> 
    forall O O' t, 
      sdom_ O' t td' -> 
      get O abstcblsid = Some (abstcblist tls) -> 
      get O' abstcblsid = Some (abstcblist tls') ->
      get O' freetid = get O freetid ->
      sdom_ O t td'.
Proof.
  introv Hts.
  induction Hts; introv Hsub Hsd Hgtls Hgtls' Hgeqf.
  
  - assert (Hgeqt: get O abstcblsid = get O' abstcblsid) by congruence. 
    unfold sdom_ in *.
    destruct Hsd as [Heat | Heft].
    + unfold ex_active_tsk in *.
      rewrite Hgeqt. auto.
    + right.
      unfold ex_free_tsk in *.
      rewrite <- Hgeqf. auto.
      
  -
    assert (Hsub': Maps.sub tls_used' tls').
    {
      eapply sub_join_set_sub; eauto.
    }
    specialize (IHHts Hsub' (set O abstcblsid (abstcblist tls')) O' t0 Hsd).
    specializes IHHts; eauto.
    rewrite map_get_set.
    auto.
    rewrite neq_set_get; eauto.
    introv Hf; inverts Hf.

    assert (Hgu: get tls_used t = Some (p, st, msg0, sus0, td)).
    {
      unfolds in H. jeat.
    }
    assert (Hgt: get tls t = Some (p, st, msg0, sus0, td)).
    {
      unfolds in Hsub.
      simpljoin. jeat.
    }
    
    lets H_: tickchange_sdom_prsv_rev IHHts Hgtls.
    eapply H_; eauto.
    rewrite map_get_set; auto.
    rewrite neq_set_get; eauto. introv Hf; inverts Hf.

  -
    assert (Hsub_: Maps.sub tls_used' tls_used).
    {
      unfolds in H.
      unfolds.
      eexists. jeat.
    }
    assert (Hsub': Maps.sub tls_used' tls).
    {
      eapply sub_trans; eauto.
    }
    specialize (IHHts Hsub').
    eapply IHHts; eauto.
Qed. 
     
Lemma tickisr_spec_sdom_prsv_rev:
  forall t O ac vl' O' t0 td
         (Htckspc : tickisr_spec t nil O ac (vl', O'))
         (Hsd: sdom O' t0 td),
    sdom O t0 td.  
Proof. 
  intros.
  unfolds in Htckspc.
  destruct Htckspc as (tls & qls & ctid & dtmp & dt & cdmp & cd & cid_ & Hgct &
                         Hgt & Hgtls & Hgqls & Hgdtmp & Hgdt & Hact & Hgcmp & Hgcd & Hex).
  
  destruct Hex as (tls' & qls' & Hstep & Hif).
  subst ac.
  
  d_if_hyp.
  
  - (* case where current domain changes *)

    destruct Hif as (imp & lmp & ldmp & scdmp & idx & len & ld & schd & H'). 
    destruct H' as (Hgimp & Hgidx & Hglmp & Hglen & Hgldmp &
                      Hgld & Hgscdmp & Hgschd & H'). 
    
    d_mt_hyp.
    *
      destruct p. 
      unfolds in Hstep.
      destruct H'; subst O'.
      eapply tickstep_prsv_sdom_rev with (O:=O) in Hsd; eauto.
      { apply sub_refl. }
      {
        do 5 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
        rewrite map_get_set.
        auto.
      }
      {
        repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      }
    *
      destruct H'.
      subst.
      auto.
  -
    destruct Hif.
    subst O'.
    eapply tickstep_prsv_sdom_rev with (O:=O) in Hsd; eauto.
    { apply sub_refl. }
    {
      do 2 (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
      rewrite map_get_set.
      auto.
    }
    {
      repeat (rewrite neq_set_get; eauto; try (introv Hf; inverts Hf)).
    }
Qed.   

Lemma dr_tick_handler: 
  forall t, 
  deduct_rules t get_hprio_in_dom (rly_itp_env t) (guar_itp_env t) flows_to
    obsr_equiv_data tickisr q_star. 
Proof.
  intros.
  constructors.
  - (* tickisr_spec *)  
    instantiate (1:=q_star).
    constructors.
    + apply stable_pre_trivial_asrt.
    + introv Hpre1 Htckspc.
      destruct Hpre1 as (Hp & Hinv).
      splits.
      * unfold post1.
        splits; eauto.
        ** eapply tickisr_spec_inv_prsv; eauto.
        ** unfolds.
           split.
           *** introv Hsd.
               eapply tickisr_spec_sdom_prsv; eauto.
           *** introv Hqsd.
               eapply tickisr_spec_q_sdom_prsv; eauto.
      *
        split.
        **
          eapply tickisr_spec_sdom_prsv; eauto.
        **
          eapply tickisr_spec_sdom_prsv_rev; eauto.
      *
        intros.
        inverts Htckspc.
        simpljoin; tryfalse. 
      * 
        introv Hf.
        false. apply Hf.
        inverts Htckspc.
        simpljoin.
        eexists; eauto.
    +
      introv Hpre2 Htck1 Htck2 Hnex1 Hnex2.
      unfolds in Htck1; simpljoin.
      false; apply Hnex1.
      eexists; eauto.

  -
    introv Hinv Hq Hs.
    subst s2.
    split.
    + simpl. unfolds. auto.
    + apply dr_sched.
Qed.   

  
