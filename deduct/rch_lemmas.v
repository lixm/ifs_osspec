
Require Import memory.
Require Import language. 
Require Import opsem.
Require Import rules.
Require Import properties.
Require Import my_tacs. 

Section RchLemmas.

Context {state_t : Type}.  
Context `{State state_t}.

Fixpoint has_itp (ks: cont) :=
  match ks with
  | kstop => False
  | kenknl f strat ks' => has_itp ks'
  | kevent _ _ _ => True
  end. 

Definition good_stmt t sd (rly_tsk guar_tsk rly_itp guar_itp: rg_env_t) flt dteq O s ks :=  
    head_sat t O s /\
      exists q,
      (has_itp ks /\ deduct_rules t sd (rly_itp t) (guar_itp t) flt dteq s q \/
         ~has_itp ks /\ deduct_rules t sd (rly_tsk t) (guar_tsk t) flt dteq s q).  

Fixpoint good_cont
  (t: tid) (sd: ossched) (rly_tsk guar_tsk rly_itp guar_itp: rg_env_t) flt dteq O ks := 
  match ks with
  | kstop => True
  | kenknl f strat ks' =>
      good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks' 
  | kevent i c ks' =>
      match c with
      | cur_stmt s =>
          good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks' /\ 
            good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks'   
      | cur_strat strat =>
          good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks'   
      end
  end.
    
Definition good_ctrl
  (t: tid) (sd: ossched) (rly_tsk guar_tsk rly_itp guar_itp: rg_env_t) flt dteq O (C: code) :=
  match C with
  | (c, ks) =>
      match c with
      | cur_stmt s =>
          good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks /\
            good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks
      | cur_strat strat =>
          good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks
      end
  end.


Lemma not_end_ssp_simp:
  forall s t O q, 
    ~ (exists vl, s = END vl) ->
    (sat_stmt_post t O s q <-> head_sat t O s). 
Proof.
  introv Hne.
  split.
  -
    introv Hssp.
    destruct s; simpl in Hssp; simpl; auto.
  -
    introv Hhs.
    unfold sat_stmt_post.
    destruct s; simpl; auto.
    false.
    apply Hne.
    eexists; eauto.
Qed.         

Definition stable_stmt t s rly :=
  forall O O',
    head_sat t O s ->
    (rly O O' \/ swi_changes O O') ->
    head_sat t O' s.

Lemma rule_stable_stmt:
  forall t sd rly guar flt dteq s q, 
    deduct_rules t sd rly guar flt dteq s q ->
    stable_stmt t s rly.
Proof.
  introv Hrule.
  induction Hrule.
  - eauto.
  - unfold stable_stmt in *.
    introv Hhs Hor.
    simpl in Hhs.
    lets H_: IHHrule Hhs Hor.
    simpl.
    auto.
  - unfold stable_stmt in *.
    introv Hhs Hor.
    simpl.
    eapply IHHrule; eauto.
  - unfold stable_pre in *.
    unfold stable_stmt.
    introv Hhs Hor.
    simpl in Hhs.
    simpl.
    eapply H0; eauto.
  - unfold stable_stmt.
    introv Hhs Hor.
    simpl. auto.
Qed. 

Lemma good_stmt_guar_itp_preserved:
  forall t t' sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O O' s ks, 
    well_rg rly_tsk guar_tsk rly_itp guar_itp -> 
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks ->
    guar_itp t' O O' -> 
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' s ks. 
Proof.
  introv Hwrg Hgs Hg.
  unfold good_stmt in *.
  destruct Hgs as (Hssp & q & Hor).
  split.
  2: {
    exists q.
    auto.
  }          
  unfold well_rg in Hwrg.
  destruct Hwrg as (Hid & Hincl).
  destruct (Hincl t' t O O') as (He & Hne).
  destruct (He Hg) as (Hrly_t & Hrly_i).
  destruct Hor as [(Hhi & Hdr) | (Hnhi & Hdr)].
  -
    lets Hstb: rule_stable_stmt Hdr.
    unfold stable_stmt in Hstb.
    eapply Hstb; eauto.
  -
    lets Hstb: rule_stable_stmt Hdr.
    unfold stable_stmt in Hstb.
    eapply Hstb; eauto.
Qed. 

Lemma no_itp_in_cont_good_cont: 
  forall t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks, 
    ~has_itp ks -> 
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks.  
Proof.
  induction ks; introv Hni.
  - simpl. auto.
  - simpl. eapply IHks; eauto.
  - simpl in Hni.
    false. apply Hni; auto.
Qed. 

Lemma good_cont_guar_preserved:
  forall ks t t' sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O O', 
    well_rg rly_tsk guar_tsk rly_itp guar_itp -> 
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks ->
    (~has_itp ks /\ guar_tsk t' O O' \/ has_itp ks /\ guar_itp t' O O') ->
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' ks. 
Proof.
  induction ks; introv Hwrg Hgc Hor.
  -
    simpl; auto.
  -
    simpl in Hgc.
    simpl.
    eapply IHks; eauto.
  -
    simpl in Hgc.
    simpl.
    simpl in Hor.
    destruct Hor.
    + destruct H0. false. apply H0; auto.
    + destruct H0 as (_ & Hgi).
      destruct c eqn: E.
      * destruct Hgc.
        assert (Hitpor: ~has_itp ks \/ has_itp ks) by tauto.
        split.
        eapply good_stmt_guar_itp_preserved; eauto.
        destruct Hitpor as [Hni | Hi].
        ** 
          apply no_itp_in_cont_good_cont; auto.
        **
          eapply IHks; eauto.
      *
        assert (Hitpor: ~has_itp ks \/ has_itp ks) by tauto.
        destruct Hitpor as [Hni | Hi].
        **
          apply no_itp_in_cont_good_cont; auto.
        **
          eapply IHks; eauto.
Qed.   

Lemma good_stmt_spec_step_preserved:
  forall t sd rly guar flt dteq s q, 
    deduct_rules t sd rly guar flt dteq s q -> 
    forall O, 
      I O -> 
      sat_stmt_post t O s q ->    
      forall s' O' ac,  
        spec_step sd t s O s' O' ac ->
        (deduct_rules t sd rly guar flt dteq s' q /\
           I O' /\
           (* get O coretid = get O' coretid /\ *)
           sat_stmt_post t O' s' q /\
           (O = O' \/ guar O O')). 
Proof.
  introv Hdr.
  assert (Hdr_:=Hdr).
  (* remember s as stmt.  *)
  induction Hdr; introv Hinv (* Hvc *) Hssp Hstep.
  -
    inverts Hstep.
    split.
    constructors; eauto.
    assert (H_: pre1 t O p).
    {
      unfolds. splits; eauto.
    }
    lets H__: H1 H_ H8.
    destruct H__ as (Hpost & Hsdeq & Hcre & Htck).
    unfolds in Hpost.
    destruct Hpost as (Hq & HI' & Hguar).
    split; eauto.
  -
    inverts Hstep.
    rename H9 into Hsteps1.
    + (* s1 terminates *)
      simpl in Hssp.
      assert (Hsat: sat_stmt_post t O s1 q').
      {
        inverts Hsteps1; simpl; auto.
      }
      lets H_: IHHdr Hdr Hinv (* Hvc *) Hsat Hsteps1.
      destruct H_ as (Hdr' & Hinv' & Hssp' & Hguar).
      simpl in Hssp'.
      specialize (H0 _ _ _ Hinv' Hssp' (eq_refl _)).
      destruct H0.
      splits; eauto.
    + (* s1 does not terminate *)
      rename H5 into Hsteps1.
      assert (Hsat: sat_stmt_post t O s1 q').
      {        
        inverts Hsteps1; simpl; auto.
      }
      lets H_: IHHdr Hdr Hinv (* Hvc *) Hsat Hsteps1.
      destruct H_ as (Hdr' & Hinv' & Hssp' & Hguar).
      apply not_end_ssp_simp in Hssp'; auto.      
      splits; eauto.      
      constructors; eauto.
  -
    inverts Hstep. 
    splits; eauto.
    constructors; eauto.
    introv Hinv_ Hq' Hif.
    destruct (b vl) eqn: EE.
    + subst s2.
      split; auto.
      simpl. eapply H0; eauto.
    + subst s2.
      split.
      * simpl. eapply H1; eauto.
      * constructors; auto.
  -
    inverts Hstep.
    splits; eauto.
    + constructors; eauto.
    + simpl. eapply H1; eauto.
      unfolds.
      split; eauto.
  -
    inverts Hstep.
Qed.

Lemma step_hs_ssp:
  forall sd t cd O cd' O' ac q, 
    spec_step sd t cd O cd' O' ac ->
    head_sat t O cd ->
    sat_stmt_post t O cd q. 
Proof.
  introv Hstep Hhs.
  inverts Hstep; simpl; simpl in Hhs; auto.
Qed. 

Lemma ssp_hs:
  forall t O cd q, 
    sat_stmt_post t O cd q ->
    head_sat t O cd.
Proof.
  introv Hssp.
  destruct cd; simpl in Hssp; simpl; auto.
Qed. 

Lemma good_ctrl_knl_step_preserved:
  forall t aspc ispc (sd: ossched) rly_tsk guar_tsk rly_itp guar_itp flt dteq (* uprgs *) kspc C C' O O' sst sst' ac, 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (* uprgs *) kspc ->
    kspc = (aspc, ispc, sd) -> 
    I O ->
    (* valid_ct t O cid ->   *)
    good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C ->
    hapistep kspc t C sst O C' sst' O' ac ->
    (I O' /\ good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' C' /\
       (* (get O coretid = get O' coretid) /\  *) 
       (has_itp (snd C) /\ guar_itp t O O' \/ ~has_itp (snd C) /\ guar_tsk t O O')). 
Proof.
  introv Htr Hkspc Hinv (* Hvc *) Hgcl Hstep.
  inverts Hstep.
  
  - (* entrance to API *)
    inverts Htr.
    rename H9 into Hapicond.
    inv_tuple. inv_tuple.
    specializes Hapicond; eauto.
    instantiate (1:=t) in Hapicond.
    destruct Hapicond as (Hhs & Hrule).
    lets H_: Hhs Hinv.
    splits; eauto.
    + unfold good_ctrl.
      split.
      2: {
        simpl; auto.
      }
      unfold good_stmt.
      split.
      rename H5 into Hgstmts.
      eapply Hgstmts in H3; eauto.
      (* rewrite not_end_ssp_simp; eauto. *)
      destruct Hrule as (q & Hrule).
      exists q.
      right.
      split; eauto.
    + (* O and O' in guar *)
      right.
      split.
      simpl. introv Hf. inverts Hf.
      rename H6 into Hwrg.
      unfold well_rg in Hwrg.
      destruct Hwrg as (Hid & Hincl).
      destruct (Hid t O').
      auto.

  - (* executing API or interrupt handler *)
    rename H0 into Hsstep.
    unfold good_ctrl in Hgcl.
    destruct Hgcl as (Hgs & Hgc).
    unfold good_stmt in Hgs.
    destruct Hgs as (Hssp & (q & Hor)).
    destruct Hor as [Hitp | Htsk].
    +
      subst kspc.
      destruct Hitp as (Hhi & Hdr).
      lets H_: step_hs_ssp q Hsstep Hssp.
      lets H__: good_stmt_spec_step_preserved Hdr Hinv (* Hvc *) H_. clear H_.
      lets H_: H__ Hsstep; clear H__.
      destruct H_ as (Hdr' & Hinv' & Hssp' & Hguar').
      splits; eauto.
      unfold good_ctrl.
      split.
      *
        unfold good_stmt.
        split; eauto.
        eapply ssp_hs; eauto.
      *
        destruct Hguar' as [Hid | Hg].
        ** subst; auto.
        **
          eapply good_cont_guar_preserved; eauto.
          inverts Htr; auto.
      *
        simpl. left.
        split; eauto.
        inverts Htr.
        rename H3 into Hwrg.
        unfold well_rg in Hwrg.
        destruct Hwrg as (Hid & Hincl).
        destruct Hguar' as [HeqOO' | HguarOO']; auto.
        subst O.
        destruct (Hid t O'); auto.
    +
      subst kspc.
      destruct Htsk as (Hnhi & Hdr).
      lets H_: step_hs_ssp q Hsstep Hssp.
      lets H__: good_stmt_spec_step_preserved Hdr Hinv (* Hvc *) H_. clear H_.
      lets H_: H__ Hsstep; clear H__.
      destruct H_ as (Hdr' & Hinv' & Hssp' & Hguar').
      splits; eauto.
      unfold good_ctrl.
      split.
      *
        unfold good_stmt.
        split; eauto.
        eapply ssp_hs; eauto.
      *
        destruct Hguar' as [Hid | Hg].
        ** subst; auto.
        **
          eapply good_cont_guar_preserved; eauto.
          inverts Htr; auto.
      *
        simpl. right. 
        split; eauto.
        inverts Htr.
        rename H3 into Hwrg.
        unfold well_rg in Hwrg.
        destruct Hwrg as (Hid & Hincl).
        destruct Hguar' as [HeqOO' | HguarOO']; auto.
        subst O.
        destruct (Hid t O'); auto.
        
  - (* exiting API function *)
    simpl in Hgcl.
    splits; eauto.
    simpl.
    destruct Hgcl; auto.
    inverts Htr.
    rename H3 into Hwrg.
    unfold well_rg in Hwrg.
    destruct Hwrg as (Hid & Hincl).
    specialize (Hid t O').
    destruct Hid.
    simpl.
    assert (Hitpor: ~has_itp ks \/ has_itp ks) by tauto.
    destruct Hitpor.
    + right; split; eauto.
    + left; split; eauto.

  - (* exiting interrupt handler *) 
    simpl in Hgcl.
    destruct Hgcl as (Hgstmt & Hrem).
    splits; eauto.
    
    inverts Htr.
    rename H2 into Hwrg.
    unfold well_rg in Hwrg.
    destruct Hwrg as (Hid & Hincl).
    specialize (Hid t O').
    destruct Hid.
    simpl.
    left. 
    split; eauto.
Qed. 

Lemma good_ctrl_task_step_preserved:
  forall t aspc ispc (sd: ossched) rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) kspc C C' O O' ac ust ust', 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) kspc ->
    kspc = (aspc, ispc, sd) -> 
    I O ->
    (* valid_ct t O cid ->   *)
    good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C ->
    htstep kspc t C ust O C' ust' O' ac -> 
    (I O' /\ good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' C' /\
       (* (get O coretid = get O' coretid) /\  *)
       (has_itp (snd C) /\ guar_itp t O O' \/ ~has_itp (snd C) /\ guar_tsk t O O')). 
Proof.
  introv Htr Hkspc Hinv (* Hvc *) Hgc Hstep.
  inverts Hstep.
  
  - (* task step based on step of user program *)
    splits; eauto.
    inverts Htr.
    inverts H.
    rename H4 into Hwrg.
    unfold well_rg in Hwrg.
    destruct Hwrg as (Hid & Hincl).
    destruct (Hid t O').
    assert (Hitpor: ~has_itp ks \/ has_itp ks) by tauto.
    destruct Hitpor.
    + right; split; eauto.
    + left; split; eauto.

  - (* task step based on step of kernel *)
    eapply good_ctrl_knl_step_preserved; eauto.
Qed. 

Lemma good_stmt_guar_preserved_neqt:
  forall t t' sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O O' s ks, 
    well_rg rly_tsk guar_tsk rly_itp guar_itp -> 
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks ->
    guar_itp t' O O' \/ guar_tsk t' O O' -> 
    t' <> t -> 
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' s ks. 
Proof.
  introv Hwrg Hgs Hg Hneqt.
  unfold good_stmt in *.
  destruct Hgs as (Hhs & q & Hor).
  split.
  2: {
    exists q.
    auto.
  }          
  unfold well_rg in Hwrg.
  assert (Hrly: rly_tsk t O O' /\ rly_itp t O O').
  {
    destruct Hg.
    eapply Hwrg in H0; eauto.
    eapply Hwrg in Hneqt; eauto.
  }
  destruct Hrly as (Htly_tsk & Hrly_itp).
  destruct Hor as [(Hhi & Hdr) | (Hnhi & Hdr)]. 
  -
    lets Hstb: rule_stable_stmt Hdr.
    unfold stable_stmt in Hstb.
    eapply Hstb; eauto.
  -
    lets Hstb: rule_stable_stmt Hdr.
    unfold stable_stmt in Hstb.
    eapply Hstb; eauto.
Qed. 

Lemma good_cont_guar_preserved_neqt:
  forall ks t t' rly_tsk guar_tsk rly_itp guar_itp sd flt dteq O O', 
    well_rg rly_tsk guar_tsk rly_itp guar_itp -> 
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks -> 
    guar_itp t' O O' \/ guar_tsk t' O O' -> 
    t' <> t -> 
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' ks.
Proof.
  induction ks; introv Hwrg Hgc Hg Hneqt.
  -
    simpl; auto.
  -
    simpl. simpl in Hgc.
    eapply IHks; eauto.
  -
    simpl; simpl in Hgc.
    destruct c.
    + 
      destruct Hgc; split.
      eapply good_stmt_guar_preserved_neqt; eauto.
      eapply IHks; eauto.
    +
      eapply IHks; eauto.
Qed. 

Lemma good_ctrl_guar_preserved_neqt: 
  forall t t' sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O O' C, 
    well_rg rly_tsk guar_tsk rly_itp guar_itp -> 
    good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C -> 
    guar_itp t' O O' \/ guar_tsk t' O O' -> 
    t' <> t -> 
    good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' C. 
Proof.
  introv Hwrg Hgc Hguar Hneqt.
  unfold good_ctrl in *.
  destruct C as (c, ks).
  destruct c.
  - 
    destruct Hgc.
    split.
    +
      eapply good_stmt_guar_preserved_neqt; eauto.
    +
      eapply good_cont_guar_preserved_neqt; eauto.
  -
    eapply good_cont_guar_preserved_neqt; eauto.
Qed.            

Lemma good_stmt_tcre_neqt: 
  forall t sd rly guar flt dteq cd q,
    deduct_rules t sd rly guar flt dteq cd q ->
    forall aspc O cd' O' t' fp argp, 
      head_sat t O cd ->
      I O -> 
      spec_step aspc t cd O cd' O' (_TCreAct t' fp argp) ->
      t <> t'. 
Proof.
  introv Hdr.
  induction Hdr; introv Hhs Hinv Hstep.
  -
    simpl in Hhs.
    assert (Hpre1: pre1 t O p).
    {
      unfolds. split; eauto.
    }
    inverts Hstep.
    specializes H1; eauto.
    destruct H1 as (Hpost1 & (* Hcdeq &  *)Htdeq & Hval_integ & Hconfid).
    specialize (Hval_integ _ _ _ (eq_refl _)).
    destruct Hval_integ; auto.
  -
    simpl in Hhs.
    inverts Hstep.
    + 
      eapply IHHdr; eauto.
    +
      eapply IHHdr; eauto.
  -
    inverts Hstep.
  -
    inverts Hstep.
  -
    inverts Hstep.
Qed. 

Lemma good_stmt_swi_preserved:
  forall t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O O' s ks,
    (* well_sched aspc ispc sd I dteq sdom ->  *)
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O s ks ->
    swi_changes O O' ->     
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' s ks. 
Proof.
  introv Hgstm Hswic.  
  inverts Hgstm.
  destruct H1 as (q & Hor).
  destruct Hor as [(Hhi & Hdr) | (Hni & Hdr)].
  - lets Hstable: rule_stable_stmt Hdr.
    unfold good_stmt.
    split.
    eapply Hstable; eauto.
    exists q.
    left; split; auto.
  - lets Hstable: rule_stable_stmt Hdr.
    unfold good_stmt.
    split.
    eapply Hstable; eauto.
    exists q.
    right; split; auto.
Qed. 

Lemma good_cont_swi_preserved:
  forall ks t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O O',
    (* well_sched kspc I dteq sdom ->  *)
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O ks ->
    swi_changes O O' ->     
    good_cont t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' ks. 
Proof.
  induction ks; introv Hgc Hswi.
  -
    simpl; auto.
  -
    simpl.
    simpl in Hgc.
    eapply IHks; eauto.
  -
    simpl in Hgc; simpl.
    destruct c.
    +
      destruct Hgc; split.
      eapply good_stmt_swi_preserved; eauto.
      eapply IHks; eauto.
    +
      eapply IHks; eauto.
Qed.

Lemma good_stmt_swi_exe_preserved:
  forall t rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) kspc aspc ispc sd asrt vs ks O O', 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) kspc ->
    kspc = (aspc, ispc, sd) -> 
    I O -> 
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O (sched asrt;;> vs) ks -> 
    swi_changes O O' -> 
    good_stmt t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' (vs nil) ks.  
Proof.
  introv Htr Hkspc Hinv Hgstm Hsw.
  subst kspc.
  unfold good_stmt in *.
  destruct Hgstm as (Hhs & Hex).
  simpl in Hhs.
  destruct Hex as (q & Hor).
  destruct Hor as [(Hhi & Hdr) | (Hni & Hdr)].
  -
    inverts Hdr.           
    inverts H8.
    assert (Hpre1: pre1 t O asrt).
    {
      unfolds. 
      split; auto.
    }
    assert (Hq': q' t nil O) by eauto.
    specialize (H10 _ _ _ Hinv Hq' (eq_refl _)).
    destruct H10 as (Hssp & Hdr_rem).
    lets Hstable: rule_stable_stmt Hdr_rem.
    eapply ssp_hs in Hssp; eauto.    
    split.
    + eapply Hstable; eauto.
    + exists q. left; split; auto.
  -
    inverts Hdr.           
    inverts H8.
    assert (Hpre1: pre1 t O asrt).
    {
      unfolds. 
      split; auto.
    }
    assert (Hq': q' t nil O) by eauto.
    specialize (H10 _ _ _ Hinv Hq' (eq_refl _)).
    destruct H10 as (Hssp & Hdr_rem).
    lets Hstable: rule_stable_stmt Hdr_rem.
    eapply ssp_hs in Hssp; eauto.    
    split.
    + eapply Hstable; eauto.
    + exists q. right; split; auto.
Qed.

Lemma good_ctrl_sys_step_preserved:
  forall t aspc ispc (sd: ossched) rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs kspc T T' O O' ust ust' act, 
    top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (*uprgs*) kspc ->
    kspc = (aspc, ispc, sd) ->
    I O ->
    (forall t C, T t = Some C -> good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C) ->
    hpstep uprgs kspc T ust O T' ust' O' (act, t) ->
    (I O' /\ 
       (forall t C, T' t = Some C -> good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O' C)).   
Proof.
  introv Htr Hkspc Hinv Hgc Hstep.
  inverts Hstep.

  - (* system step based on task step *)
    (* assert (Hvc: valid_ct t O cid). *)
    (* { *)
    (*   unfolds. eexists; splits; eauto. *)
    (* } *)
    lets Hgct: Hgc t C.  specializes Hgct; eauto.
    lets H_: good_ctrl_task_step_preserved Htr Hkspc Hinv (* Hvc *) Hgct.
    specializes H_; eauto.
    destruct H_ as (Hinv' & Hgctrl' & Hor).
    split; auto.
    introv Hgt0.
    casetac t t0 Ht Hf.
    +
      subst.
      rewrite upd_task_pool_eq in Hgt0.
      inverts Hgt0.
      auto.
    +
      rewrite upd_task_pool_neq in Hgt0; eauto.
      specializes Hgc; eauto.
      eapply good_ctrl_guar_preserved_neqt; eauto.
      inverts Htr; auto.
      destruct Hor; simpljoin; eauto.

  - (* entrance to some interrupt handler *)
    inv_htistep.
    inv_tuple.
    split; auto.
    introv Hget.
    casetac t t0 Ht Hf.
    + subst.
      rewrite upd_task_pool_eq in Hget. 
      inverts Hget.
      specializes Hgc; eauto.
      simpl.
      inverts Htr.
      inv_tuple.
      rename H9 into Henitp.
      specialize (Henitp i l0 t0).
      specializes Henitp; eauto.
      destruct Henitp as (Hhs & Hdr_itp).
      specialize (Hhs O' Hinv).
      split.
      *
        destruct Hdr_itp as (q & Hdr_itp).
        unfold good_stmt.
        split; auto.
        exists q.
        left. simpl. split; auto.
      *
        simpl in Hgc.
        destruct c; auto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.

  - (* context switch *)
    split.
    {
      inverts Htr.
      inverts H9. (* well_sched *) 
      unfolds in ws_sched_inv.
      inv_tuple. inv_tuple.
      specializes ws_sched_inv; eauto.
    }
    {
      inv_tuple.
      introv Hget.
      casetac t t0 Ht Hf.

      - (* current task *) 
        specializes Hgc; eauto.
        subst.
        rewrite upd_task_pool_eq in Hget.
        inverts Hget.
        simpl in Hgc; simpl.
        destruct Hgc as (Hgstm & Hgcont).
        split.
        +
          eapply good_stmt_swi_exe_preserved; eauto.
          unfolds. eexists; eauto.
        +
          inverts Htr; 
            eapply good_cont_swi_preserved; eauto.
          unfolds; eexists; eauto.
          
      - (* different task *)
        rewrite upd_task_pool_neq in Hget; eauto.
        specializes Hgc; eauto.
        destruct C as [c_ ks_].
        simpl in Hgc; simpl.
        destruct c_.
        + 
          inverts Htr. 
          destruct Hgc; split.
          eapply good_stmt_swi_preserved; eauto.
          unfolds; eexists; eauto.
          eapply good_cont_swi_preserved; eauto.
          unfolds; eexists; eauto.
        +
          inverts Htr. 
          eapply good_cont_swi_preserved; eauto.
          unfolds; eexists; eauto.          
    }
      
  - (* task creation *)
    (* assert (Hvc: valid_ct t O cid). *)
    (* { *)
    (*   unfolds. eexists; splits; eauto. *)
    (* } *) 
    lets H__: Hgc.
    specializes H__; eauto.
    lets H_: good_ctrl_task_step_preserved Htr Hkspc Hinv (* Hvc *) H__.
    rename H__ into Hgctrl.
    specializes H_; eauto.
    destruct H_ as (Hinv' & Hgctrl' & Hor).
    split; auto.
    introv Hget.
    assert (Hneqt: t <> t').
    {
      inv_htstep.
      inv_hapistep. 
      inverts Hgctrl. 
      inverts H0.
      destruct H10 as (q & Hor_).
      destruct Hor_ as [(Hhi & Hdr_) | (Hnhi & Hdr_)]; 
        eapply good_stmt_tcre_neqt; eauto.
    }
    casetac t' t0 Heq1 Hneq1.
    +
      subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      simpl. auto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.
      casetac t t0 Heq2 Hneq2.
      *
        subst.
        rewrite upd_task_pool_eq in Hget.
        inverts Hget.
        auto.
      *
        rewrite upd_task_pool_neq in Hget; eauto.
        specializes Hgc; eauto.
        eapply good_ctrl_guar_preserved_neqt with (t':=t) (t:=t0); eauto.
        inverts Htr; auto.
        destruct Hor; simpljoin; auto.
        
  - (* task deletion *)
    lets H__: Hgc. 
    specializes H__; eauto.
    lets H_: good_ctrl_task_step_preserved Htr Hkspc Hinv (* Hvc *) H__.
    rename H__ into Hgctrl.
    specializes H_; eauto.
    destruct H_ as (Hinv' & Hgctrl' & Hor).
    split; auto.
    introv Hget.
    casetac t t0 Heq Hne.
    +
      subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      auto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.
      specialize (Hgc _ _ Hget).
      eapply good_ctrl_guar_preserved_neqt with (t':=t) (t:=t0); eauto.
      inverts Htr; auto.
      destruct Hor; simpljoin; auto.      
Qed.


(* Definition ct_core (O: state_t) := *)
(*   forall t cid td, cur_tsk O cid t -> sdom O t td -> core_of_dom O td cid.   *)

(* Lemma ct_core_spec_step_preserved: *)
(*   forall sd t s rly guar flt dteq q,  *)
(*     deduct_rules t sd rly guar flt dteq s q ->      *)
(*     forall O s' O' ac, *)
(*       head_sat t O s ->  *)
(*       spec_step sd t s O s' O' ac ->  *)
(*       I O -> *)
(*       ct_core O -> *)
(*       ct_core O'.  *)
(* Proof. *)
(*   introv Hdr. *)
(*   induction Hdr; introv Hhs Hstep Hinv Hcc. *)
(*   - *)
(*     simpl in Hhs. *)
(*     assert (pre1 t O p). *)
(*     { unfolds. split; auto. } *)
(*     inverts Hstep. *)
(*     specializes H1; eauto. *)
(*     destruct H1 as (Hpost & Hcdeq & Htdeq & Hcre & Htick).     *)
(*     inverts Hpost; simpljoin. *)
(*     unfold ct_core in *. *)
(*     introv Hvc' Hsd'. *)
(*     assert (Hct_: cur_tsk O cid t0). *)
(*     { *)
(*       eapply H14; eauto. *)
(*     } *)
(*     assert (Hsd_: sdom O t0 td). *)
(*     { *)
(*       eapply Htdeq; eauto. *)
(*     } *)
(*     specializes Hcc; eauto. *)
(*     eapply Hcdeq; auto. *)
(*   -  *)
(*     simpl in Hhs. *)
(*     inverts Hstep. *)
(*     +  *)
(*       eapply IHHdr; eauto. *)
(*     + *)
(*       eapply IHHdr; eauto. *)
(*   - *)
(*     inverts Hstep. *)
(*     auto. *)
(*   - *)
(*     inverts Hstep. *)
(*     auto. *)
(*   - *)
(*     inverts Hstep. *)
(* Qed. *)
  
(* Lemma ct_core_knl_step_preserved: *)
(*   forall t (sd: ossched) rly_tsk guar_tsk rly_itp guar_itp flt dteq kspc C C' O O' sst sst' ac,  *)
(*     (* top_rule rly_tsk guar_tsk rly_itp guar_itp I sdom flt dteq uprgs kspc -> *) *)
(*     (* kspc = (aspc, ispc, sd) ->  *) *)
(*     sd = snd kspc ->  *)
(*     good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C -> *)
(*     I O -> *)
(*     ct_core O ->  *)
(*     hapistep kspc t C sst O C' sst' O' ac -> *)
(*     ct_core O'.  *)
(* Proof. *)
(*   introv Hsd Hgctrl Hinv Hcc Hastp. *)
(*   inverts Hastp; try (eauto; fail). *)

(*   inverts Hgctrl. *)
(*   inverts H1; simpljoin. (* good_stmt *)  *)
(*   destruct H1; simpljoin; eapply ct_core_spec_step_preserved; eauto.  *)
(* Qed.  *)

(* Lemma ct_core_task_step_preserved: *)
(*   forall t (sd: ossched) rly_tsk guar_tsk rly_itp guar_itp flt dteq kspc C C' O O' ac ust ust',  *)
(*     (* top_rule rly_tsk guar_tsk rly_itp guar_itp I sdom flt dteq uprgs kspc -> *) *)
(*     (* kspc = (aspc, ispc, sd) ->  *) *)
(*     sd = snd kspc ->  *)
(*     good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C -> *)
(*     I O -> *)
(*     ct_core O ->  *)
(*     htstep kspc t C ust O C' ust' O' ac ->  *)
(*     ct_core O'.  *)
(* Proof. *)
(*   introv Hsd Hgctrl Hinv Hcc Htstp. *)
(*   inverts Htstp; auto. *)
(*   eapply ct_core_knl_step_preserved; eauto. *)
(* Qed. *)


Lemma sched_same_cur_dom :
  forall O O' cid td t' sd, 
    I O ->
    cur_dom O cid td ->
    sd O td t' ->
    upd_cur_tsk O cid t' O' -> 
    (forall cid td, cur_dom O cid td <-> cur_dom O' cid td). 
Proof.
  introv Hinv Hcd Hsd Huct.
  eapply upd_cur_tsk_prsv_cur_dom; eauto.
Qed. 

(* Lemma ct_core_sys_step_preserved: *)
(*   forall t aspc ispc (sd: ossched) rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs kspc T T' O O' ust ust' act,  *)
(*     top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq uprgs kspc -> *)
(*     kspc = (aspc, ispc, sd) -> *)
(*     (forall t C, T t = Some C -> good_ctrl t sd rly_tsk guar_tsk rly_itp guar_itp flt dteq O C) -> *)
(*     I O -> *)
(*     ct_core O ->  *)
(*     hpstep uprgs kspc T ust O T' ust' O' (act, t) -> *)
(*     ct_core O'.   *)
(* Proof. *)
(*   introv Htr Hkspc Hgc Hinv Hcc Hstep. *)
(*   inverts Hstep. *)
(*   - *)
(*     specializes Hgc; eauto. *)
(*     subst kspc. *)
(*     lets H__: ct_core_task_step_preserved Hgc; eauto. *)
(*     simpl; auto. *)
(*   - *)
(*     match goal with H: context[htistep] |- _ => inverts H end. *)
(*     auto. *)
(*   - *)
(*     inverts Htr. *)
(*     inverts H8. (* well_sched *)  *)
(*     (* rename H11 into Hssd. (* sched_same_dom *)  *) *)
(*     (* rename H16 into Hpdom. (* sched_preserves_dom *)  *) *)
(*     specializes Hgc; eauto. *)
(*     unfold ct_core. *)
(*     introv Hvc Hsdom. *)
(*     inv_tuple. inv_tuple. *)
(*     (* destruct Hvc as (ct0 & Hget & Hgett). *) *)
(*     (* rewrite map_get_set in Hget. *) *)

(*     unfold sched_same_dom in ws_sched_eqdom. *)
    
(*     lets H_: ws_sched_eqdom Hinv H3 H4 H5. *)
 
(*     casetac cid cid0 He Hne. *)
(*     + *)
(*       subst. *)
(*       assert (Hct': cur_tsk O' cid0 t'). *)
(*       { *)
(*         eapply upd_cur_tsk_eq; eauto. *)
(*       } *)
(*       assert (Hinv': I O'). *)
(*       { *)
(*         eapply ws_sched_inv; eauto. *)
(*       } *)
(*       assert (Hteq: t0 = t'). *)
(*       { *)
(*         eapply cur_tsk_is_fn; eauto. *)
(*       } *)
(*       subst t0. *)
(*       assert (Hsd': sdom O t' td). *)
(*       { *)
(*         eapply ws_sch_in_dom; eauto. *)
(*       } *)
(*       eapply H_ in Hsd'; eauto. *)
(*       assert (Htdeq: td0 = td). *)
(*       { *)
(*         eapply sdom_is_fn; eauto. *)
(*       } *)
(*       subst td0. *)
(*       assert (Hcurd: cur_dom O' cid0 td). *)
(*       {         *)
(*         lets H__: sched_same_cur_dom Hinv H3 H4 H5. *)
(*         eapply H__; auto. *)
(*       } *)
(*       eapply ws_cd_cod; eauto. *)
(*     + *)
(*       assert (Hct_: cur_tsk O cid0 t0). *)
(*       {         *)
(*         lets H__: upd_cur_tsk_neq (not_eq_sym Hne) H5. *)
(*         eapply H__ in Hvc; eauto. *)
(*       } *)
(*       assert (Hsd_: sdom O t0 td0). *)
(*       { *)
(*         eapply H_ in Hsdom; eauto. *)
(*       } *)
(*       assert (Hcd_: core_of_dom O td0 cid0). *)
(*       { *)
(*         eapply Hcc; eauto. *)
(*       } *)
(*       lets H__: ws_sched_eqcodm Hinv H3 H4 H5. *)
(*       eapply H__; eauto. *)
(*   - *)
(*     specializes Hgc; eauto. *)
(*     lets H__: ct_core_task_step_preserved Hgc Hinv Hcc; eauto. *)
(*     subst. simpl; auto. *)
(*   -     *)
(*     specializes Hgc; eauto. *)
(*     lets H__: ct_core_task_step_preserved Hgc Hinv Hcc; eauto. *)
(*     subst. simpl; auto. *)
(* Qed.  *)


Inductive succ: spec_code -> spec_code -> Prop :=
| prim_succ:
  forall p vl step vl', 
    succ (spec_prim p vl step) (spec_done vl')
| sched_succ:
  forall p vl', 
    succ (sched p) (spec_done vl')
| seq_succ1:
  forall s s' ss,
    succ s s' ->
    succ (spec_seq s ss) (spec_seq s' ss)
| seq_succ2:
  forall vl s ss s', 
    succ (ss vl) s' -> 
    succ (spec_seq s ss) s'
| seq_succ3:
  forall s ss vl', 
    succ (spec_seq s ss) (ss vl')
| seq_succ4:
  forall s ss vl', 
    succ (spec_seq s ss) (spec_done vl')
| dowh_succ0:
  forall s b, 
    succ (spec_dowh s b) (spec_seq s (fun vl => if b vl then (spec_dowh s b) else spec_done vl))
| dowh_succ1:
  forall s s' b,
    succ s s' -> 
    succ (spec_dowh s b) (spec_seq s' (fun vl => if b vl then (spec_dowh s b) else spec_done vl))
| dowh_succ2:
  forall s b vl, 
    succ (spec_dowh s b) (if b vl then (spec_dowh s b) else spec_done vl)
| dowh_succ3:
  forall s b,
    succ (spec_dowh s b) (spec_dowh s b)
| dowh_succ4:
  forall s b vl,
    succ (spec_dowh s b) (spec_done vl). 
         
Definition succ_eq s s' := s = s' \/ succ s s'.

Lemma spec_step_has_tick':
  forall sd t cid s O s' O', 
    spec_step sd t s O s' O' (_TickAct cid) ->
    exists vl', has_tick' s t cid O vl' O'.
Proof.
  introv Hssp.
  remember (_TickAct cid) as tac.
  induction Hssp; try rewrite Heqtac in *.
  -
    simpl.
    eexists; eauto.
  -
    inverts Heqtac.
  -
    specializes IHHssp; eauto.
    destruct IHHssp. 
    exists x.
    simpl. left; auto.
  -
    specializes IHHssp; eauto.
    destruct IHHssp. 
    exists x.
    simpl. left; auto.
  -
    inverts Heqtac.
Qed. 

Lemma succ_has_tick': 
  forall s s', 
    succ s s' ->
    forall s'' sd t O O' cid, 
      spec_step sd t s' O s'' O' (_TickAct cid) ->
      exists vl', has_tick' s t cid O vl' O'. 
Proof.
  introv Hse.
  induction Hse; introv Hstep; 
    try (inverts Hstep; eauto; fail).
  -
    inverts Hstep.
    +
      simpl.
      specializes IHHse; eauto.
      destruct IHHse; eexists; left; eauto.
    +
      simpl.
      specializes IHHse; eauto.
      destruct IHHse; eexists; left; eauto.
  -
    specializes IHHse; eauto.
    simpl. destruct IHHse. exists x. right.
    eexists;eauto.
  -
    simpl.
    eapply spec_step_has_tick' in Hstep; eauto.
    destruct Hstep.
    exists x. right; eexists; eauto.
  -
    eapply spec_step_has_tick' in Hstep; eauto.
    destruct Hstep as (vl' & Hht).
    simpl in Hht.
    simpl.
    destruct Hht.
    + eexists; eauto.
    + destruct H0.
      destruct (b x) eqn: Ebx.
      * simpl in H0. eexists; eauto.
      * simpl in H0; tryfalse. 
  -
    destruct (b vl) eqn: E.
    +
      eapply spec_step_has_tick' in Hstep; eauto.
    +
      inverts Hstep.
Qed.         

Inductive head_step: spec_code -> osabstep -> vallist -> Prop := 
| head_prim:
    forall p vl step, head_step (spec_prim p vl step) step vl
| head_seq:
  forall s1 step vs2 vl, 
    head_step s1 step vl -> 
    head_step (spec_seq s1 vs2) step vl. 

Lemma succ_has_tick'_preserved:
  forall s s', 
    succ s s' ->
    forall t cid O vl' O', 
      has_tick' s' t cid O vl' O' ->
      has_tick' s t cid O vl' O'.
Proof.
  introv Hsuc.
  induction Hsuc; introv Htck'; try (simpl in Htck'; tryfalse; fail).
  - simpl in Htck'.
    destruct Htck' as [Htck' | Htck'].
    eapply IHHsuc in Htck'; eauto.
    simpl. left; auto.
    destruct Htck' as (vl_ & Hht).
    simpl. right.
    eexists; eauto.
  - eapply IHHsuc in Htck'; eauto.
    simpl. right; eexists; eauto.
  - simpl. right; eexists; eauto.
  - simpl.
    simpl in Htck'.
    destruct Htck'; auto.
    destruct H0 as (vl_ & Htck').
    destruct (b vl_) eqn: E.
    simpl in Htck'.
    auto.
    simpl in Htck'. false.
  - simpl in Htck'.
    destruct Htck' as [Htck' | Htck'].
    eapply IHHsuc in Htck'; eauto.
    destruct Htck' as (vl_ & Htck').
    destruct (b vl_) eqn: E.
    simpl in Htck'.
    auto.
    simpl in Htck'. false.
  - destruct (b vl) eqn: E. 
    auto.
    simpl in Htck'. false.
  - auto.
Qed. 


Lemma spec_step_has_tick'_vl': 
  forall s s' t cid sd O O', 
    spec_step sd t s O s' O' (_TickAct cid) ->
    exists step vl,
      head_step s step vl /\
        forall vl' O O', step t vl O (_TickAct cid) (vl', O') -> has_tick' s t cid O vl' O'.
Proof.
  introv Hss.
  remember (_TickAct cid) as act.
  induction Hss.
  - 
    exists step vl.
    split.
    + constructors; eauto.
    + introv Hstep.
      rewrite Heqact in *.
      assert (has_tick' (asrt # step [|vl|]) t cid O0 vl'0 O'0).
      { simpl. auto. }
      auto.
  -
    inverts Heqact.
  -
    rewrite Heqact in *.
    specialize (IHHss (eq_refl _)).
    destruct IHHss as (step & vl_ & Hhs & Hall).
    exists step vl_.
    split.
    constructors; eauto.
    introv Hstp.
    eapply Hall in Hstp; eauto.
    simpl. left. auto.
  -
    rewrite Heqact in *.
    specialize (IHHss (eq_refl _)).
    destruct IHHss as (step & vl_ & Hhs & Hall).
    exists step vl_.
    split.
    constructors; eauto.
    introv Hstp.
    eapply Hall in Hstp; eauto.
    simpl. left. auto.
  -
    inverts Heqact. 
Qed.     

Lemma succ_has_tick'_vl': 
  forall s' s'' t cid sd O O', 
    spec_step sd t s' O s'' O' (_TickAct cid) ->
    forall s, 
      succ s s' ->
      exists step vl,
        head_step s' step vl /\
          forall vl' O O', step t vl O (_TickAct cid) (vl', O') -> has_tick' s t cid O vl' O'.
Proof.
  introv Hssp Hsuc.
  lets H__: spec_step_has_tick'_vl' Hssp.
  destruct H__ as (step & vl & Hhs & Hall).
  exists step vl.
  split; auto.
  introv Hstep.
  eapply Hall in Hstep; eauto.
  eapply succ_has_tick'_preserved; eauto.
Qed.

Lemma succ_eq_has_tick'_vl':
  forall s' s'' t cid sd O O', 
    spec_step sd t s' O s'' O' (_TickAct cid) ->
    forall s, 
      succ_eq s s' ->
      exists step vl,
        head_step s' step vl /\
          forall vl' O O', step t vl O (_TickAct cid) (vl', O') -> has_tick' s t cid O vl' O'.
Proof.
  introv Hstep Hse.
  destruct Hse as [He|Hne].
  - subst. eapply spec_step_has_tick'_vl'; eauto.
  - eapply succ_has_tick'_vl'; eauto.
Qed. 

Lemma head_step_deter: 
  forall s step vl, 
    head_step s step vl ->
    forall O1 O2 O1' O2' s1' s2' t sd cid, 
    (forall vl1' vl2',
        step t vl O1 (_TickAct cid) (vl1', O1') ->
        step t vl O2 (_TickAct cid) (vl2', O2')
        -> vl1' = vl2') -> 
    I O1 -> I O2 -> 
    spec_step sd t s O1 s1' O1' (_TickAct cid) ->
    spec_step sd t s O2 s2' O2' (_TickAct cid) ->
    s1' = s2'. 
Proof.
  introv Hhs.
  induction Hhs; introv Hstep12 Hinv1 Hinv2 Hstep1 Hstep2.
  - inverts Hstep1; inverts Hstep2.
    specializes Hstep12; eauto.
    congruence.
  -
    inverts Hstep1; inverts Hstep2.
    + 
      lets H__: IHHhs Hstep12 Hinv1 Hinv2.
      specializes H__; eauto.
      congruence. 
    + 
      lets H__: IHHhs Hstep12 Hinv1 Hinv2.
      specializes H__; eauto.
      false. subst s1'. apply H10; eexists; eauto.
    +
      lets H__: IHHhs Hstep12 Hinv1 Hinv2.
      specializes H__; eauto.
      false. subst s1'0. apply H9; eexists; eauto.
    +
      lets H__: IHHhs Hstep12 Hinv1 Hinv2.
      specializes H__; eauto.
      congruence. 
Qed. 

(* Lemma head_step_deter:  *)
(*   forall s step vl O1 O2 O1' O2' s1' s2' ac t sd,  *)
(*     head_step s step vl -> *)
(*     (exists vl0, forall vl' O O', I O -> step t vl O ac (vl', O') -> vl' = vl0) -> *)
(*     I O1 -> I O2 ->  *)
(*     spec_step sd t s O1 s1' O1' ac -> *)
(*     spec_step sd t s O2 s2' O2' ac -> *)
(*     s1' = s2'.  *)
(* Proof. *)
(*   induction s; introv Hhdstep Hex Hinv1 Hinv2 Hstep1 Hstep2; *)
(*     inverts Hhdstep. *)
(*   -  *)
(*     inverts Hstep1; inverts Hstep2. *)
(*     destruct Hex. *)
(*     lets H1_: H0 Hinv1 H5; eauto. *)
(*     lets H2_: H0 Hinv2 H6; eauto. *)
(*     congruence. *)
(*   - *)
(*     inverts Hstep1; inverts Hstep2. *)
(*     +  *)
(*       lets H__: IHs H5 Hex H11 H10; eauto. *)
(*       congruence.  *)
(*     + *)
(*       lets H__: IHs H5 Hex H10 H6; eauto. *)
(*       rewrite <- H__ in *. *)
(*       false. apply H12; eexists; eauto. *)
(*     + *)
(*       lets H__: IHs H5 Hex H6 H12; eauto. *)
(*       rewrite H__ in *. *)
(*       false. apply H11. eexists; eauto. *)
(*     + *)
(*       lets H__: IHs H5 Hex H6 H7; eauto. *)
(*       subst. auto. *)
(* Qed. *) 

(* Lemma head_step_deter:  *)
(*   forall s step vl O1 O2 O1' O2' s1' s2' ac t sd,  *)
(*     head_step s step vl -> *)
(*     (exists vl0, forall vl' O O', step t vl O ac (vl', O') -> vl' = vl0) -> *)
(*     spec_step sd t s O1 s1' O1' ac -> *)
(*     spec_step sd t s O2 s2' O2' ac -> *)
(*     s1' = s2'.  *)
(* Proof. *)
(*   induction s; introv Hhdstep Hex Hstep1 Hstep2; inverts Hhdstep. *)
(*   -  *)
(*     inverts Hstep1; inverts Hstep2. *)
(*     destruct Hex. *)
(*     lets H1_: H0 H5; eauto. *)
(*     lets H2_: H0 H6; eauto. *)
(*     congruence. *)
(*   - *)
(*     inverts Hstep1; inverts Hstep2. *)
(*     +  *)
(*       lets H__: IHs H5 Hex H11 H10. *)
(*       congruence.  *)
(*     + *)
(*       lets H__: IHs H5 Hex H10 H6. *)
(*       rewrite <- H__ in *. *)
(*       false. apply H12; eexists; eauto. *)
(*     + *)
(*       lets H__: IHs H5 Hex H6 H12. *)
(*       rewrite H__ in *. *)
(*       false. apply H11. eexists; eauto. *)
(*     + *)
(*       lets H__: IHs H5 Hex H6 H7. *)
(*       subst. auto. *)
(* Qed. *) 

Lemma succ_eq_has_tick': 
  forall s s', 
    succ_eq s s' ->
    forall s'' sd t O O' cid, 
      spec_step sd t s' O s'' O' (_TickAct cid) ->
      exists vl', has_tick' s t cid O vl' O'. 
Proof.
  introv Hse Hstep.
  destruct Hse as [Heq | Hsuc].
  subst.
  eapply spec_step_has_tick'; eauto.
  eapply succ_has_tick'; eauto.
Qed. 

Lemma succ_s_end:
  forall s vl, (~exists vl_, s = spec_done vl_) -> succ s (spec_done vl).
Proof.
  induction s; intros; try (constructors; fail).
  false. apply H0; eexists; eauto.
Qed. 

Lemma spec_done_no_succ:
  forall s s', 
    succ s s' ->
     ~exists vl, s = spec_done vl. 
Proof.
  introv Hsuc.
  inverts Hsuc; try (introv Hf; simpljoin; tryfalse; fail). 
Qed. 
  
Lemma succ_trans:
  forall s1 s2, 
    succ s1 s2 ->
    forall s3, 
      succ s2 s3 ->
      succ s1 s3.
Proof. 
  introv Hsuc12.
  induction Hsuc12; introv Hsuc;
    try (inverts Hsuc; fail); 
    try (constructors; eauto; fail); 
    try (inverts Hsuc; constructors; eauto; fail).
  -
    inverts Hsuc; try constructors; eauto.
    destruct (b vl) eqn: E; auto.
    inverts H3.
  -
    inverts Hsuc; try (constructors; eauto). 
    destruct (b vl) eqn: E.
    auto.
    inverts H3.
  -
    destruct (b vl) eqn: E.
    auto.
    inverts Hsuc.
Qed. 

Lemma spec_step_succ:
  forall sd t s O s' O' ac, 
    spec_step sd t s O s' O' ac ->
    succ s s'. 
Proof.
  introv Hstep.
  induction Hstep; try (constructors; eauto; fail).  
Qed. 

Lemma succ_spec_step_preserved:
  forall sd t s s' O' s'' O'' ac, 
    spec_step sd t s' O' s'' O'' ac ->
    succ s s' ->
    succ s s''.
Proof.
  introv Hstep Hsuc.
  eapply spec_step_succ in Hstep; eauto.
  eapply succ_trans; eauto.
Qed.

Definition stmt_succ_eq (aspc: osapispec) (ispc: osintspec) s :=
  (exists f ac ft vl, aspc f = Some (ac, ft) /\ succ_eq (ac vl) s) \/
    (exists i s0, ispc i = Some s0 /\ succ_eq s0 s). 

Fixpoint cont_succ_eq (aspc: osapispec) (ispc: osintspec) (ks: cont) :=
  match ks with 
  | kstop => True
  | kenknl f strat ks => cont_succ_eq aspc ispc ks
  | kevent i c ks =>
      match c with
        cur_stmt s' => stmt_succ_eq aspc ispc s' /\ cont_succ_eq aspc ispc ks
      | cur_strat strat => cont_succ_eq aspc ispc ks
      end
  end.

Definition ctrl_succ_eq (aspc: osapispec) (ispc: osintspec) (C: code) :=
  match C with
    (c, ks) =>
      match c with
      | cur_stmt s => stmt_succ_eq aspc ispc s /\ cont_succ_eq aspc ispc ks
      | cur_strat _ => cont_succ_eq aspc ispc ks
      end
  end.
  
Lemma ctrl_succ_eq_knl_step_preserved:
  forall t aspc ispc (sd: ossched) kspc C C' O O' sst sst' ac, 
    kspc = (aspc, ispc, sd) -> 
    ctrl_succ_eq aspc ispc C -> 
    hapistep kspc t C sst O C' sst' O' ac ->
    ctrl_succ_eq aspc ispc C'. 
Proof.
  introv Hkspc Hcs Hstep.
  destruct C as (c & ks).
  inverts Hstep.

  - simpl.
    split; auto.
    unfolds. left.
    inverts H0.
    do 3 eexists; exists vl; split; eauto.
    unfolds. left; auto.

  - simpl in Hcs; simpl.
    destruct Hcs as (Hsse & Hcse).
    split.
    +
      unfold stmt_succ_eq in Hsse; unfold stmt_succ_eq.
      destruct Hsse as [Hase | Hise].
      *
        left.
        destruct Hase as (f & ac_ & ft & vl & Haf & Hse).
        unfolds in Hse.
        destruct Hse.
        ** subst.
           do 3 eexists.
           exists vl.
           split; eauto.
           eapply spec_step_succ in H4; eauto.
           unfolds; right; eauto.
        ** 
          do 4 eexists; split; eauto.
          right.
          eapply succ_spec_step_preserved; eauto.
      *
        right.
        destruct Hise as (i & s0 & His0 & Hsucce).
        unfolds in Hsucce.
        destruct Hsucce.
        ** subst.
           do 2 eexists.
           split; eauto.
           right.
           eapply spec_step_succ; eauto.
        ** do 2 eexists; split; eauto.
           right. 
           eapply succ_spec_step_preserved; eauto.
    +
      auto.
      
  - 
    simpl.
    simpl in Hcs.
    simpljoin; auto.
    
  -
    simpl in Hcs.
    simpljoin.
    simpl; auto.
Qed.

Lemma ctrl_succ_eq_task_step_preserved:
  forall t (sd: ossched) kspc aspc ispc C C' O O' ac ust ust', 
    kspc =(aspc, ispc, sd) -> 
    ctrl_succ_eq aspc ispc C -> 
    htstep kspc t C ust O C' ust' O' ac ->
    ctrl_succ_eq aspc ispc C'. 
Proof.
  introv Hkspc Hcse Hstep.
  inverts Hstep.
  - auto.
  - eapply ctrl_succ_eq_knl_step_preserved; eauto.
Qed.

Lemma ctrl_succ_eq_sys_step_preserved:
  forall t aspc ispc (sd: ossched) uprgs kspc T T' O O' ust ust' act, 
    kspc = (aspc, ispc, sd) ->
    (forall t C, T t = Some C -> ctrl_succ_eq aspc ispc C) -> 
    hpstep uprgs kspc T ust O T' ust' O' (act, t) ->
    (forall t C, T' t = Some C -> ctrl_succ_eq aspc ispc C).  
Proof.
  introv Hkspc Hactrl Hstep.
  introv Hget.
  inverts Hstep.
  -
    casetac t t0 He Hne.
    + subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      specializes Hactrl; eauto.
      eapply ctrl_succ_eq_task_step_preserved; eauto.
    + rewrite upd_task_pool_neq in Hget; eauto.
  -
    inv_tuple.
    casetac t t0 He Hne.
    +
      subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      specializes Hactrl; eauto.
      inverts H14.
      simpl in Hactrl; simpl.
      split; auto.
      unfolds.
      right. do 2 eexists; splits; eauto.
      unfolds; left; auto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.
  -
    casetac t t0 He Hne.
    +
      subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      specializes Hactrl; eauto.
      unfolds in Hactrl.
      destruct Hactrl as (Hsc & Hic).
      simpl; split; eauto.
      unfolds in Hsc.
      destruct Hsc.
      * 
        simpljoin.
        unfolds. left.
        do 3 eexists. exists x2.
        split; eauto.
        assert (succ_eq (sched asrt;;> vs) (vs nil)).
        { right. constructors; eauto. } 
        destruct H2; destruct H0; tryfalse.
        rewrite H2. right; constructors; eauto.
        rewrite H2. right; constructors; eauto.
        right. rewrite H0 in H2. auto.
        right. eapply succ_trans; eauto.
      *
        simpljoin.
        unfolds. right. 
        do 2 eexists; split; eauto.
        destruct H2.
        rewrite H0. right; constructors; eauto.
        right.
        assert (succ (sched asrt;;> vs) (vs nil)).
        { constructors; eauto. }
        eapply succ_trans; eauto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.
      
  -
    casetac t' t0 He Hne.
    +
      subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      simpl. auto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.
      casetac t t0 He' Hne'.
      * 
        subst. 
        rewrite upd_task_pool_eq in Hget.
        inverts Hget.
        specializes Hactrl; eauto.
        eapply ctrl_succ_eq_task_step_preserved; eauto.
      *
        rewrite upd_task_pool_neq in Hget; eauto.
        
  -
    casetac t t0 He Hne.
    +
      subst.
      rewrite upd_task_pool_eq in Hget.
      inverts Hget.
      specializes Hactrl; eauto.
      eapply ctrl_succ_eq_task_step_preserved; eauto.
    +
      rewrite upd_task_pool_neq in Hget; eauto.
Qed. 

      
End RchLemmas.
