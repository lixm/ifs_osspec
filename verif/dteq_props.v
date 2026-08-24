
Require Import memory.
Require Import state.
Require Import rules.

Require Import int_auto.
Require Import my_tacs.

Require Import specs_common.
Require Import obsr_equiv.

Lemma dteq_tasks_refl: 
  forall td O, obsr_equiv_tasks td O O.
Proof.
  intros.
  unfolds.
  split.
  - split; intro; auto.
  - introv Hg1 Hg2.
    assert (tls1 = tls2) by congruence.
    subst. 
    split.
    + split; intro; auto.
    + introv Hgtls1 Hgtls2 Hgtd.
      rewrite Hgtls1 in Hgtls2.
      inverts Hgtls2.
      splits; auto.
Qed.

Lemma dteq_mqs_refl:
  forall td O, obsr_equiv_mqs td O O.
Proof.
  intros.
  unfolds.
  split.
  - split; intro; auto.
  - introv Hg1 Hg2.
    assert (qls1 = qls2) by congruence.
    subst.
    split.
    + split; intro; auto.
    + introv Hgqls1 Hgqls2 Hgd.
      congruence.
Qed.

Lemma dteq_chs_refl:
  forall td O, obsr_equiv_chans td O O.
Proof.
  intros.
  unfolds.
  split.
  - split; intro; auto.
  - introv Hg1 Hg2.
    assert (chs1 = chs2) by congruence.
    subst.
    split.
    + split; intro; auto.
    + introv Hgc1 Hgc2.
      rewrite Hgc1 in Hgc2. inverts Hgc2.
      split.
      * split; auto.
      * intros.
        split; auto.
Qed.         

Lemma dteq_fts_refl:
  forall td O, obsr_equiv_freetids td O O.
Proof.
  intros.
  unfolds.
  split.
  - split; intro; auto.
  - introv Hg1 Hg2.
    rewrite Hg1 in Hg2; inverts Hg2.
    tauto.
Qed.    

Lemma dteq_fqs_refl:
  forall td O, obsr_equiv_freeqids td O O. 
Proof.
  intros.
  unfolds.
  split.
  - split; intro; auto.
  - introv Hg1 Hg2.
    rewrite Hg1 in Hg2; inverts Hg2.
    tauto.
Qed.     

Lemma dteq_schd_refl:
  forall O, obsr_equiv_schd O O.
Proof.
  intros.
  constructors; auto.
Qed.

Lemma obsr_equiv_tskd_refl:
  forall td O, obsr_equiv_tskd td O O.
Proof.
  intros.
  constructors.
  apply dteq_tasks_refl.
  +
    apply dteq_mqs_refl.
  +
    apply dteq_chs_refl.
  +
    apply dteq_fts_refl.
  +
    apply dteq_fqs_refl.
Qed.   

Lemma obsr_equiv_data_refl:
  forall d O, obsr_equiv_data d O O.  
Proof.
  intros.
  unfolds.
  destruct d.
  -
    apply obsr_equiv_tskd_refl. 
  -
    apply dteq_schd_refl.
Qed.


Lemma dteq_tasks_sym:
  forall td O1 O2, 
    obsr_equiv_tasks td O1 O2 ->
    obsr_equiv_tasks td O2 O1.
Proof.
  introv Hdte_t.
  unfold obsr_equiv_tasks in *.
  destruct Hdte_t as (Heqv & Hall).
  split.
  - tauto.
  - introv Hg2 Hg1.
    specialize (Hall _ _ t Hg1 Hg2).
    destruct Hall as (Heqv_ & Hall_).
    split.
    + tauto.
    + introv Hgtls1 Hgtls2 Hgd.
      specializes Hall_; eauto.
      * 
        subst d1.
        assert (Hex: ex_tsk_in_dom t td tls1).
        {
          unfolds. do 4 eexists; eauto.
        }
        eapply Heqv_ in Hex; eauto.
        unfolds in Hex.
        simpljoin.
        rewrite H in Hgtls2; inverts Hgtls2; eauto.
      *
        simpljoin; splits; eauto.
Qed.

Lemma dteq_mqs_sym: 
  forall td O1 O2, 
    obsr_equiv_mqs td O1 O2 -> 
    obsr_equiv_mqs td O2 O1. 
Proof.
  introv Hdte_q.
  unfold obsr_equiv_tasks in *.
  destruct Hdte_q as (Heqv & Hall).
  split.
  - tauto.
  - introv Hg2 Hg1.
    specialize (Hall _ _ q Hg1 Hg2).
    destruct Hall as (Heqv_ & Hall_).
    split.
    + tauto.
    + introv Hgqls1 Hgqls2 Hgd.
      specializes Hall_; eauto.
      * 
        subst d1.
        assert (Hex: ex_mq_in_dom q td qls1).
        {
          unfolds. destruct mq1. do 3 eexists; eauto.
        }
        eapply Heqv_ in Hex; eauto.
        unfolds in Hex.
        simpljoin.
        rewrite H in Hgqls2; inverts Hgqls2; eauto.
Qed. 

Lemma dteq_chs_sym:
  forall td O1 O2, 
    obsr_equiv_chans td O1 O2 ->
    obsr_equiv_chans td O2 O1.
Proof.
  introv Hdte_ch.
  unfold obsr_equiv_chans in *.
  destruct Hdte_ch as (Heqv & Hall).
  split.
  - tauto.
  - introv Hg2 Hg1.
    lets H__: Hall chid Hg1 Hg2.
    clear Hall.
    destruct H__ as (Heqv_ & Hall).
    split.
    + tauto.
    + introv Hgc1 Hgc2.
      specializes Hall; eauto.
      destruct Hall as (Hsde & Hdde & Heq).
      splits; eauto.
      {
        introv Hd1.
        rewrite Hdde in Heq.
        apply Heq in Hd1.
        simpljoin; split; auto.
      }
Qed.         

Lemma dteq_fts_sym: 
  forall td O1 O2, 
    obsr_equiv_freetids td O1 O2 ->
    obsr_equiv_freetids td O2 O1. 
Proof.
  introv Hoef.
  unfold obsr_equiv_freetids in *.
  destruct Hoef as (Heqv & Hall).
  split.
  - tauto.
  - introv Hgf2 Hgf1.
    lets H__: Hall ts Hgf1 Hgf2.
    tauto.
Qed.     

Lemma dteq_fqs_sym: 
  forall td O1 O2, 
    obsr_equiv_freeqids td O1 O2 ->
    obsr_equiv_freeqids td O2 O1. 
Proof.
  introv Hoef.
  unfold obsr_equiv_freeqids in *.
  destruct Hoef as (Heqv & Hall).
  split.
  - tauto.
  - introv Hgf2 Hgf1.
    lets H__: Hall qs Hgf1 Hgf2.
    tauto.
Qed.

Lemma obsr_equiv_tskd_sym:
  forall td O1 O2,
    obsr_equiv_tskd td O1 O2 ->
    obsr_equiv_tskd td O2 O1.
Proof.
  introv Hoe.
  inverts Hoe.
  constructors.
  - apply dteq_tasks_sym; auto.
  - apply dteq_mqs_sym; auto.
  - apply dteq_chs_sym; auto.
  - apply dteq_fts_sym; auto.
  - apply dteq_fqs_sym; auto.
Qed.     

Lemma dteq_schd_sym:
  forall O1 O2, 
    obsr_equiv_schd O1 O2 ->
    obsr_equiv_schd O2 O1. 
Proof.
  introv Hoes.
  inverts Hoes.
  constructors; eauto.
Qed. 

Lemma obsr_equiv_data_sym:
  forall d O1 O2,
    obsr_equiv_data d O1 O2 ->
    obsr_equiv_data d O2 O1.
Proof.
  introv Hdte.
  unfold obsr_equiv_data in *.
  destruct d.
  -
    inverts Hdte.
    constructors.
    +
      apply dteq_tasks_sym; auto.
    +
      apply dteq_mqs_sym; auto.
    +
      apply dteq_chs_sym; auto.
    +
      apply dteq_fts_sym; auto.
    +
      apply dteq_fqs_sym; auto.
  -
    apply dteq_schd_sym; auto.
Qed.       



Lemma dteq_tasks_trans: 
  forall td O1 O2 O3, 
    obsr_equiv_tasks td O1 O2 ->
    obsr_equiv_tasks td O2 O3 ->
    obsr_equiv_tasks td O1 O3. 
Proof.
  introv Hdt12 Hdt23.
  unfold obsr_equiv_tasks in *.
  destruct Hdt12 as (Heqv12 & Hall12).
  destruct Hdt23 as (Heqv23 & Hall23).
  split.
  - tauto.
  - introv Hg1 Hg3.
    assert (Hex2: exists tls, get O2 abstcblsid = Some (abstcblist tls)).
    {
      eapply Heqv12; eauto.
    }
    rename tls2 into tls3.
    destruct Hex2 as (tls2 & Hg2).
    lets H12_: Hall12 t Hg1 Hg2; eauto.
    lets H23_: Hall23 t Hg2 Hg3; eauto.
    clear Hall12 Hall23.
    destruct H12_ as (Heq12 & Hall12).
    destruct H23_ as (Heq23 & Hall23).
    split.
    + tauto.
    + introv Hg1_ Hg3_ Hd1.
      subst d1.
      assert (Hex2: ex_tsk_in_dom t td tls2).
      { 
        eapply Heq12; eauto.
        unfolds. do 4 eexists; eauto.
      }
      unfolds in Hex2.
      rename pr2 into pr3.
      rename st2 into st3.
      rename msg2 into msg3.
      rename sus2 into sus3.

      destruct Hex2 as (pr2 & st2 & m2 & sus2 & Hg2_).
      lets H_: Hall12 Hg1_ Hg2_; eauto.
      lets H__: Hall23 Hg2_ Hg3_; eauto.
      specialize (H_ (eq_refl _)).
      specialize (H__ (eq_refl _)).
      simpljoin; splits; congruence.
Qed.

Lemma dteq_mqs_trans: 
  forall td O1 O2 O3, 
    obsr_equiv_mqs td O1 O2 ->
    obsr_equiv_mqs td O2 O3 ->
    obsr_equiv_mqs td O1 O3. 
Proof.
  introv Hdt12 Hdt23.
  unfold obsr_equiv_mqs in *.
  destruct Hdt12 as (Heqv12 & Hall12).
  destruct Hdt23 as (Heqv23 & Hall23).
  split.
  - tauto.
  - introv Hg1 Hg3.
    assert (Hex2: exists qls, get O2 quelsid = Some (absecblist qls)).
    {
      eapply Heqv12; eauto.
    }
    rename qls2 into qls3.
    destruct Hex2 as (qls2 & Hg2).
    lets H12_: Hall12 q Hg1 Hg2; eauto.
    lets H23_: Hall23 q Hg2 Hg3; eauto.
    clear Hall12 Hall23.
    destruct H12_ as (Heq12 & Hall12).
    destruct H23_ as (Heq23 & Hall23).
    split.
    + tauto.
    + introv Hg1_ Hg3_ Hd1.
      subst d1.
      assert (Hex2: ex_mq_in_dom q td qls2).
      { 
        eapply Heq12; eauto.
        destruct mq1.
        unfolds. do 3 eexists; eauto.
      }
      unfolds in Hex2.
      rename mq2 into mq3.      
      destruct Hex2 as (ms2 & sz2 & ts2 & Hg2_).
      lets H_: Hall12 Hg1_ Hg2_; eauto.
      lets H__: Hall23 Hg2_ Hg3_; eauto.
      specialize (H_ (eq_refl _)).
      specialize (H__ (eq_refl _)).
      congruence.
Qed.

Lemma dteq_chs_trans: 
  forall td O1 O2 O3, 
    obsr_equiv_chans td O1 O2 ->
    obsr_equiv_chans td O2 O3 ->
    obsr_equiv_chans td O1 O3. 
Proof.
  introv Hdt12 Hdt23.
  unfold obsr_equiv_chans in *.
  destruct Hdt12 as (Heqv12 & Hall12).
  destruct Hdt23 as (Heqv23 & Hall23).
  split.
  - tauto.
  - introv Hg1 Hg3.
    assert (Hex2: exists chs, get O2 chlsid = Some (chanlist chs)).
    {
      eapply Heqv12; eauto.
    }
    rename chs2 into chs3.
    destruct Hex2 as (chs2 & Hg2).
    lets H12_: Hall12 chid Hg1 Hg2; eauto.
    lets H23_: Hall23 chid Hg2 Hg3; eauto.
    clear Hall12 Hall23.
    destruct H12_ as (Heq12 & Hall12).
    destruct H23_ as (Heq23 & Hall23).
    split.
    + tauto.
    + introv Hg1_ Hg3_.
      rename sd2 into sd3.
      rename dd2 into dd3.
      rename c2 into c3.
      assert (Hnn1: get chs1 chid <> None).
      {
        introv Hf.
        Set Printing Implicit.
        unfold DestDom in Hf.
        rewrite Hg1_ in Hf.
        inverts Hf.
        Unset Printing Implicit.        
      }
      assert (Hex2: exists sd2 dd2 c2, get chs2 chid = Some (sd2, dd2, c2)).
      {
        apply Heq12 in Hnn1.
        destruct (get chs2 chid) eqn: E2.
        destruct p. destruct p.
        do 3 eexists; eauto.
        false.
      }
      destruct Hex2 as (sd2 & dd2 & c2 & Hg2_).
      Set Printing Implicit.
      unfold DestDom in Hg2_.
      lets H12_: Hall12 Hg1_ Hg2_.
      lets H23_: Hall23 Hg2_ Hg3_.
      Unset Printing Implicit.
      destruct H12_ as (Heqsd12_ & Heqdd12_ & Heq12_).
      destruct H23_ as (Heqsd23_ & Heqdd23_ & Heq23_).

      splits; try congruence. 
      {
        introv Hsd1.
        specializes Heq12_; eauto.
        rewrite Heqdd12_ in Hsd1.
        apply Heq23_ in Hsd1.
        simpljoin.
      }
Qed. 

Lemma dteq_fts_trans: 
  forall td O1 O2 O3, 
    obsr_equiv_freetids td O1 O2 -> 
    obsr_equiv_freetids td O2 O3 -> 
    obsr_equiv_freetids td O1 O3. 
Proof.
  introv Hdt12 Hdt23.
  unfold obsr_equiv_freetids in *.
  destruct Hdt12 as (Heqv12 & Hall12).
  destruct Hdt23 as (Heqv23 & Hall23).
  split.
  - tauto.
  - introv Hg1 Hg3.
    rename fts2 into fts3.
    assert (Hex2: exists fts, get O2 freetid = Some (freetidlist fts)).
    {
      eapply Heqv12; eauto.
    }
    destruct Hex2 as (fts2 & Hg2).
    lets H12_: Hall12 ts Hg1 Hg2; eauto.
    lets H23_: Hall23 ts Hg2 Hg3; eauto.
    tauto.
Qed.     

Lemma dteq_fqs_trans: 
  forall td O1 O2 O3, 
    obsr_equiv_freeqids td O1 O2 -> 
    obsr_equiv_freeqids td O2 O3 -> 
    obsr_equiv_freeqids td O1 O3. 
Proof.
  introv Hdt12 Hdt23.
  unfold obsr_equiv_freeqids in *.
  destruct Hdt12 as (Heqv12 & Hall12).
  destruct Hdt23 as (Heqv23 & Hall23).
  split.
  - tauto.
  - introv Hg1 Hg3.
    rename fqs2 into fqs3.
    assert (Hex2: exists fqs, get O2 freeqid = Some (freeqidlist fqs)).
    {
      eapply Heqv12; eauto.
    }
    destruct Hex2 as (fts2 & Hg2).
    lets H12_: Hall12 qs Hg1 Hg2; eauto.
    lets H23_: Hall23 qs Hg2 Hg3; eauto.
    tauto.
Qed.     

Lemma obsr_equiv_tskd_trans:
  forall td O1 O2 O3, 
    obsr_equiv_tskd td O1 O2 ->
    obsr_equiv_tskd td O2 O3 ->
    obsr_equiv_tskd td O1 O3. 
Proof.
  introv Hdte12 Hdte23.
  inverts Hdte12; inverts Hdte23.
  constructors.
  -
    eapply dteq_tasks_trans; eauto.
  -
    eapply dteq_mqs_trans; eauto.
  -
    eapply dteq_chs_trans; eauto.
  -
    eapply dteq_fts_trans; eauto.
  -
    eapply dteq_fqs_trans; eauto.
Qed. 


Lemma obsr_equiv_schd_trans: 
  forall O1 O2 O3, 
    obsr_equiv_schd O1 O2 -> 
    obsr_equiv_schd O2 O3 -> 
    obsr_equiv_schd O1 O3. 
Proof.
  introv Hoe12 Hoe23.
  inverts Hoe12; inverts Hoe23.
  constructors; congruence.
Qed.


Lemma obsr_equiv_data_trans:
  forall d O1 O2 O3,
    obsr_equiv_data d O1 O2 ->
    obsr_equiv_data d O2 O3 ->
    obsr_equiv_data d O1 O3.
Proof.
  introv Hdte12 Hdte23.
  unfold obsr_equiv_data in *.
  destruct d.
  - 
    eapply obsr_equiv_tskd_trans; eauto.
  -
    eapply obsr_equiv_schd_trans; eauto.
Qed. 



(* further lemmas about obsr_equiv *) 
  
Lemma obsr_equiv_tasks_nochange: 
  forall td O1 O2, 
    get O1 abstcblsid = get O2 abstcblsid ->
    obsr_equiv_tasks td O1 O2.
Proof.
  introv Hgeq.
  unfolds.
  split.
  - rewrite Hgeq. tauto.
  - introv Hg1 Hg2.
    assert (tls1 = tls2) by congruence.
    subst. rename tls2 into tls.
    split.
    + tauto.
    + introv Hgt1 Hgt2 Htd.
      rewrite Hgt1 in Hgt2.
      inverts Hgt2.
      splits; eauto.
Qed.

Lemma obsr_equiv_mqs_nochange: 
  forall td O1 O2, 
    get O1 quelsid = get O2 quelsid ->
    obsr_equiv_mqs td O1 O2. 
Proof.
  introv Hgeq.
  unfolds.
  split.
  - rewrite Hgeq. tauto.
  - introv Hg1 Hg2.
    assert (qls1 = qls2) by congruence.
    subst. rename qls2 into qls.
    split.
    + tauto.
    + introv Hgt1 Hgt2 Htd.
      rewrite Hgt1 in Hgt2.
      inverts Hgt2.
      auto.
Qed.

Lemma obsr_equiv_chs_nochange: 
  forall td O1 O2, 
    get O1 chlsid = get O2 chlsid ->
    obsr_equiv_chans td O1 O2.  
Proof.
  introv Hgeq.
  unfolds.
  split.
  - rewrite Hgeq. tauto.
  - introv Hg1 Hg2.
    assert (chs1 = chs2) by congruence.
    subst. rename chs2 into chs.
    split.
    + tauto.
    + introv Hgc1 Hgc2.
      rewrite Hgc1 in Hgc2.
      inverts Hgc2.
      split.
      * tauto.
      * intros; splits; auto.
Qed.

Lemma obsr_equiv_fts_nochange: 
  forall td O1 O2, 
    get O1 freetid = get O2 freetid ->
    obsr_equiv_freetids td O1 O2.  
Proof.
  introv Hgeq.
  unfolds.
  rewrite Hgeq.
  split.
  - tauto.
  - introv Hg1 Hg2.
    rewrite Hg1 in Hg2.
    inverts Hg2.
    tauto.
Qed. 

Lemma obsr_equiv_fqs_nochange: 
  forall td O1 O2, 
    get O1 freeqid = get O2 freeqid ->
    obsr_equiv_freeqids td O1 O2.  
Proof.
  introv Hgeq.
  unfolds.
  rewrite Hgeq.
  split.
  - tauto.
  - introv Hg1 Hg2.
    rewrite Hg1 in Hg2.
    inverts Hg2.
    tauto.
Qed. 


