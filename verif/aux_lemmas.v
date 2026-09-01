
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
Require Import mq_apispecs.
Require Import sys_spec.

Require Import rly_guar. 
Require Import flow_policy. 
Require Import obsr_equiv.
Require Import dteq_props. 


Lemma sub_join_set_sub: 
  forall tls tls' tls0 tls0' st st' p msg sus td t,
    Maps.sub tls0 tls ->
    joinsig t (p, st, msg, sus, td) tls0' tls0 ->
    set tls t (p, st', msg, sus, td) = tls' ->
    Maps.sub tls0' tls'.
Proof.
  introv Hsub Hjoin Hset.
  apply sub_sem; eauto.
  introv Hg0.
  assert (Htneq: t0 <> t).
  {
    introv Heq.
    subst.
    unfolds in Hjoin.
    apply join_disj in Hjoin.
    eapply disjoint_sem2 in Hjoin; eauto.
    rewrite get_a_sig_a in Hjoin.
    inverts Hjoin.
  }
  assert (Hgtls0: get tls0 t0 = Some b).
  {
    jeat.
  }
  assert (Hgtls: get tls t0 = Some b).
  {
    unfolds in Hsub.
    simpljoin.
    eapply join_get_l; eauto.
  }
  clear Hgtls0.
  subst tls'.
  rewrite neq_set_get; eauto.
Qed. 


(* lemmas for remove_tid *)

Lemma beq_tid_true : forall t, beq_tid t t = true.
Proof.
  intros.
  unfolds; destruct t.
  rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_refl.
  rewrite Int.eq_true.
  simpl; auto.
Qed.

Lemma in_remove_tid_false :
  forall wl t, In t (remove_tid t wl) -> False. 
Proof.
  intro; inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  eapply IHwl; eauto.
  simpl in H.
  destruct H.
  substs.
  rewrite beq_tid_true in eq1; tryfalse.
  eapply IHwl; eauto.
Qed.

Lemma in_remove_tid :
  forall wl t ct, In ct (remove_tid t wl) -> In ct wl. 
Proof.
  inductions wl; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  simpl.
  right; eapply IHwl; eauto.
  simpl in H; destruct H; substs.
  simpl; left; auto.
  simpl; right; eapply IHwl; eauto.
Qed.

Lemma in_remove_tid' : forall wl t t', t <> t' -> In t wl -> In t (remove_tid t' wl).
Proof.
  intro; inductions wl; intros.
  simpl in H0; tryfalse.
  simpl in H0; destruct H0; substs.
  simpl.
  destruct(beq_tid t' t) eqn : eq1.
  false; apply H.
  apply beq_tid_true_eq in eq1; auto.
  simpl; auto.
  simpl.
  destruct(beq_tid t' a) eqn : eq1.
  eapply IHwl; eauto.
  simpl.
  right.
  eapply IHwl; eauto.
Qed.

(**)

Ltac inv_errp :=
  match goal with
    H: context [err_prop] |- _ => try (inverts H; simpljoin; tryfalse)
  end.

(**)

Definition q_star := fun (_ : tid) (_ : vallist) (_ : osabst) => True. 

Lemma stable_pre_trivial_asrt:
  forall t rly, 
    stable_pre t trivial_asrt rly. 
Proof.
  intros.
  unfolds.
  intros.
  unfolds.
  auto.
Qed.

(* Lemma stable_post_true: *)
(*   forall t rly,  *)
(*     stable_post t (fun (_ : tid) (_ : vallist) (_ : osabst) => True) rly. *)
(* Proof. *)
(*   intros. *)
(*   unfolds. *)
(*   intros. *)
(*   auto. *)
(* Qed.    *)


(**)

Lemma uct_ex_active_in_dom_eqv: 
  forall O t td cid t' ct, 
    ex_active_tsk O t td <-> 
    ex_active_tsk (set O coretid (oscoret (set ct cid t'))) t td. 
Proof.
  intros.
  unfold ex_active_tsk in *.
  rewrite neq_set_get; eauto.
  2: introv Hf; inverts Hf.
  tauto.
Qed. 

Lemma uct_ex_free_tsk_in_dom_eqv: 
  forall O t td cid t' ct, 
    ex_free_tsk O t td <->
      ex_free_tsk (set O coretid (oscoret (set ct cid t'))) t td. 
Proof.
  intros. 
  unfold ex_free_tsk.
  rewrite neq_set_get; eauto.
  2: introv Hf; inverts Hf.
  tauto.
Qed.   

Lemma uct_tsks_same_dom:
  forall O cid t' O', 
    upd_cur_tsk O cid t' O' -> 
    (forall t td, sdom O t td <-> sdom O' t td).
Proof.
  introv Huct.
  unfolds in Huct.
  unfold state in Huct.
  unfolds in Huct.
  simpljoin.
  unfold sdom.
  unfold state.
  unfold sdom_.
  intros.
  rewrite <- uct_ex_active_in_dom_eqv.
  rewrite <- uct_ex_free_tsk_in_dom_eqv.
  tauto.
Qed.   

(**)

Lemma ex_active_tsk_set_t_prsv: 
  forall O t t' td td' tls tsk tsk', 
    ex_active_tsk O t' td' -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some tsk -> 
    snd tsk = td -> 
    snd tsk' = td -> 
    ex_active_tsk (set O abstcblsid (abstcblist (set tls t tsk'))) t' td'. 
Proof.
  introv Heat Hgtls Hgt Hd Hd'.
  subst.
  unfold ex_active_tsk in *.
  destruct Heat as (tls0 & pr0 & st0 & msg0 & sus0 & Habs & Hget).
  rewrite map_get_set.
  uni_12_sym (get O abstcblsid).
  destruct tsk as [[[[]]]].
  destruct tsk' as [[[[]]]].
  simpl in Hd'. subst. rename t1 into td.
  casetac t t' He Hne.
  - subst.
    rewrite Hget in Hgt; inverts Hgt.
    do 5 eexists; splits; eauto.
    rewrite map_get_set; eauto.
  - do 5 eexists; splits; eauto.
    rewrite neq_set_get; eauto.
Qed.

Lemma ex_active_tsk_set_t_prsv_rev: 
  forall O t t' td td' tls tsk tsk', 
    ex_active_tsk (set O abstcblsid (abstcblist (set tls t tsk'))) t' td' -> 
    get O abstcblsid = Some (abstcblist tls) -> 
    get tls t = Some tsk -> 
    snd tsk = td -> 
    snd tsk' = td -> 
    ex_active_tsk O t' td'.
Proof.
  introv Heat Hgtls Hgt Hd Hd'.
  unfold ex_active_tsk in *.
  destruct Heat as (tls0 & pr0 & st0 & msg0 & sus0 & Habs & Hget).
  rewrite map_get_set in Habs.
  inverts Habs.
  casetac t t' He Hne.
  - subst. rewrite map_get_set in Hget.
    inverts Hget.
    destruct tsk as [[[[]]]].
    simpl in Hd'.
    subst t0.
    do 5 eexists; splits; eauto.
  - rew_neq_in Hget.
    destruct tsk as [[[[]]]].
    destruct tsk' as [[[[]]]].
    simpl in Hd. simpl in Hd'.
    subst.
    do 5 eexists; splits; eauto.
Qed.

(*  *)

Lemma tls_sdom_td_eq:
  forall O tls t pr st m sus td' td, 
    I O -> 
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (pr, st, m, sus, td') ->
    sdom O t td ->
    td' = td.
Proof.
  introv Hinv Hgtls Hgt Hsd.
  unfolds in Hsd.
  unfold state in Hsd.
  unfolds in Hsd.
  destruct Hsd as [Heat | Heft].
  -
    unfolds in Heat.
    destruct Heat as (tls0 & pr0 & st0 & msg0 & sus0 & Habs & Hget).        
    uni_12_sym (get O abstcblsid).
    uni_12_sym (get tls t).
    auto.
  -
    inverts Hinv.
    assert (Heat: ex_active_tsk O t td').
    {
      unfolds.
      do 5 eexists; splits; eauto.
    }
    assert (Hsd1: sdom O t td').
    { left. auto. }
    assert (Hsd2: sdom O t td).
    { right. auto. }
    eapply inv_tsk_d_disj; eauto.
Qed.

Lemma dte_ex_tsk_in_dom_same:
  forall td O1 O2 t0 tls1 tls2, 
    obsr_equiv_tskd td O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) ->
    (exists pr0 st m sus0, get tls1 t0 = Some (pr0, st, m, sus0, td)) <->
      (exists pr0 st m sus0, get tls2 t0 = Some (pr0, st, m, sus0, td)). 
Proof.
  introv Hoe Hg1 Hg2.
  inverts Hoe.
  unfolds in oe_td_tasks.
  destruct oe_td_tasks as (_ & Hall).
  specialize (Hall tls1 tls2 t0).
  specializes Hall; eauto.
  destruct Hall as (Heqv & Heq).
  unfold ex_tsk_in_dom in *.
  auto.
Qed. 

Lemma obsr_equiv_data_tsk_eq:
  forall td O1 O2 tls1 tls2 pr1 pr2 st1 st2 msg1 msg2 sus1 sus2 t, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) -> 
    get O2 abstcblsid = Some (abstcblist tls2) -> 
    get tls1 t = Some (pr1, st1, msg1, sus1, td) -> 
    get tls2 t = Some (pr2, st2, msg2, sus2, td) ->
    pr1 = pr2 /\ st1 = st2 /\ msg1 = msg2 /\ sus1 = sus2. 
Proof.
  introv Hoe Hgtls1 Hgtls2 Hgt1 Hgt2.
  simpl in Hoe.
  inverts Hoe.
  eapply oe_td_tasks; eauto.
Qed. 

(* *)

Definition q_bot := fun (_ : tid) (_ : vallist) (_ : osabst) => False. 

(* Lemma stable_post_qbot: *)
(*   forall t, stable_post t q_bot (rly_tsk_env t). *)
(* Proof. *)
(*   intros. *)
(*   unfolds. *)
(*   intros. *)
(*   unfolds in H. *)
(*   false.  *)
(* Qed.  *)

Lemma same_mqs_que_dom:
  forall O O' q td, 
    get O quelsid = get O' quelsid ->
    get O freeqid = get O' freeqid ->   
    q_sdom_ O q td ->
    q_sdom_ O' q td. 
Proof.
  introv Hgeq Hgeqf Hqsd.
  unfold q_sdom_ in *.
  destruct Hqsd as [Heaq | Hefq].
  - 
    left.
    unfold ex_active_que in *.
    rewrite <- Hgeq.
    auto.
  -
    right.
    unfold ex_free_que in *.
    rewrite <- Hgeqf.
    auto.
Qed.       
  
Lemma guar_tsk_refl: forall t O, guar_tsk_env t O O.
Proof.
  intros.
  unfolds.
  split; tauto.
Qed.     

(**)

Lemma ssp_end:
  forall t O vl, sat_stmt_post t O (END vl) q_star. 
Proof.
  intros.
  unfolds.
  unfold q_star.
  auto.
Qed.   

Lemma post1_same_st_q_star:
  forall t O vl', 
    I O ->
    post1 t O vl' O q_star (guar_tsk_env t). 
Proof.
  introv Hinv.
  unfolds.
  splits; eauto.
  unfolds. auto.
  unfolds.
  split.
  - intros. auto.
  - intros. auto.
Qed. 

Lemma dr_sched:
  forall t rly guar, 
    deduct_rules t rly guar flows_to obsr_equiv_data
      (sched trivial_asrt) q_star. 
Proof.
  intros.
  constructors.
  apply stable_pre_trivial_asrt.
  introv Hpre.
  unfolds; auto.
Qed.   

Lemma dr_ssp:
  forall t vl, 
    deduct_rules t (rly_tsk_env t) (guar_tsk_env t) flows_to
      obsr_equiv_data (spec_skip_step (|vl|)) q_star. 
Proof.
  intros.
  constructors.
  - 
    apply stable_pre_trivial_asrt.
  -
    introv Hpre1 Hssp.
    inverts Hssp.
    simpljoin.
    split.
    + eapply post1_same_st_q_star; eauto.
      apply Hpre1.
    + splits.
      * 
        intros. tauto.
      *
        introv Hf; inverts Hf.
      *
        intros.
        apply obsr_equiv_data_refl.
  -
    introv Hpre2 Hssp1 Hssp2 Hnex1 Hnex2.
    inverts Hssp1; inverts Hssp2; simpljoin; tryfalse.
    splits; auto.
    apply Hpre2.
Qed.       

Lemma stable_pre_tq_same_d:
  forall t q vl_, 
    stable_pre t (tsk_mq_same_dom (Vptr q :: vl_)) (rly_tsk_env t). 
Proof.
  intros.
  unfolds.
  introv Htqsd Hor.
  destruct Hor as [Hrly | Hswi].
  - unfolds in Hrly.
    unfold tsk_mq_same_dom in *.
    simpljoin.
    eexists.
    split; eauto.
  - unfolds in Hswi.
    destruct Hswi as (cid & t_ & Huct).
    lets H_: uct_tsks_same_dom Huct.
    pose proof same_mqs_que_dom as Hsqd.
    unfold tsk_mq_same_dom in *.
    destruct Htqsd as (td & Hsdt & Hsdq).
    exists td.
    split.
    + eapply H_; eauto.
    +
      unfolds in Huct. unfold state in Huct.
      unfolds in Huct. simpljoin. 
      eapply Hsqd with (O:=O); eauto.
      all: rewrite neq_set_get; eauto; try introv Hf; inverts Hf.
Qed.

(* *)


Definition chk_dom_post (vl: vallist) (t: tid) (vl': vallist) (O: osabst) := 
  (exists i, vl' = Vint32 i :: nil) /\ 
    (vl' = Vint32 dom_chk_ok :: nil -> 
     forall q vl_, 
       vl = Vptr q :: vl_ -> (exists td, sdom_ O t td /\ q_sdom_ O q td)). 

(* Lemma stable_post_chkdom: *)
(*   forall t vl,  *)
(*     stable_post t (chk_dom_post vl) (rly_tsk_env t). *)
(* Proof. *)
(*   intros. *)
(*   unfolds. *)
(*   introv Hcdp Hrly_ch. *)
(*   destruct Hrly_ch as [Hrly | Hswch]. *)
(*   - (* rly_tsk_env t O O' *) *)
(*     unfolds in Hrly. *)
(*     destruct Hrly. *)
(*     unfolds. *)
(*     split. *)
(*     { *)
(*       inverts Hcdp. *)
(*       auto. *)
(*     } *)
(*     { *)
(*       introv Hvl0 Hvl. *)
(*       subst. *)
(*       unfolds in Hcdp. *)
(*       destruct Hcdp as (_ & Hcdp). *)
(*       specializes Hcdp; eauto. *)
(*       simpljoin. *)
(*       eexists; splits; eauto. *)
(*     } *)
(*   - (* swi_changes *) *)
(*     unfolds in Hswch. *)
(*     destruct Hswch as (cid & t_ & Hupd). *)
(*     unfolds. *)
(*     split. *)
(*     { *)
(*       unfolds in Hcdp. apply Hcdp. *)
(*     } *)
(*     { *)
(*       introv Hvl0 Hvl. *)
(*       subst. *)
(*       unfolds in Hcdp. *)
(*       destruct Hcdp as (_ & Hcdp). *)
(*       specializes Hcdp; eauto. *)
(*       destruct Hcdp as (td & Hsdt & Hsdq). *)
(*       lets H_: uct_tsks_same_dom Hupd. *)
(*       specialize (H_ t td). *)
(*       exists td. *)
(*       rewrite <- H_. *)
(*       split; auto. *)
(*       destruct Hupd as (ct & ct' & Hget & Hct' & HO'). *)
(*       subst O'. *)
(*       eapply same_mqs_que_dom with (O:=O); eauto. *)
(*       all: rewrite neq_set_get; eauto; introv Hf; inverts Hf. *)
(*     } *)
(* Qed. *)     

Lemma chk_dom_post_holds:
  forall O tls t pr st msg sus td qls a vl' v0 ms sz ts td_ 
         (Hgtls : get O abstcblsid = Some (abstcblist tls))
         (Hgt : get tls t = Some (pr, st, msg, sus, td))
         (Hgqls : get O quelsid = Some (absecblist qls))
         (E1 : get qls a = Some (msgq ms sz ts, td_))
         (Horq : td = td_ /\ vl' = Vint32 dom_chk_ok :: nil \/
                   td <> td_ /\ vl' = Vint32 dom_chk_err :: nil)
         (Hexi: exists i, vl' = Vint32 i :: nil), 
    chk_dom_post (Vptr a :: v0) t vl' O.  
Proof.
  intros.
  unfolds.
  split; auto.
  introv Hvl' Hvl.
  inverts Hvl.
  destruct Horq as [Heqd | Hneqd].
  2: { simpljoin; tryfalse. }
  destruct Heqd as (Htdeq & _).
  subst.
  exists td_.
  split.
  - unfolds. left. unfolds.
    do 5 eexists; splits; eauto.
  - left. unfolds.
    do 4 eexists; splits; eauto.
Qed.

Lemma q_notin_tsk_dom_contra:
  forall t O q vl_ td tdq, 
    pre1 t O (tsk_mq_same_dom (Vptr q :: vl_)) ->
    sdom O t td ->
    tdq <> td -> 
    q_sdom_ O q tdq ->
    False. 
Proof.
  introv Hpre1 Hsd Hne Hqsd.
  unfolds in Hpre1.
  destruct Hpre1 as (Hsame & Hinv).
  unfolds in Hsame.
  destruct Hsame as (td_ & Htdt & Htdq).
  assert (Hsd': sdom O t td_).
  { unfolds. unfold state. auto. }
  assert (td = td_).
  {
    lets H__: sdom_is_fn Hinv; eauto.
  }
  subst td_.
  inverts Hinv.
  apply Hne.
  eapply inv_que_d_disj; eauto.
Qed.                      

Lemma tq_same_dom_qdom:
  forall t O vl_ td tdq qls qid ts sz ms, 
    pre1 t O (tsk_mq_same_dom (Vptr qid :: vl_)) ->
    sdom O t td ->
    get O quelsid = Some (absecblist qls) ->
    get qls qid = Some (msgq ms sz ts, tdq) ->
    tdq = td. 
Proof.
  introv Hpre1 Hsd Hgqls Hgq.
  destruct Hpre1 as (Hp & Hinv).
  unfolds in Hp.
  destruct Hp as (td_ & Hsdt & Hsdq).
  assert (Hsd_: sdom O t td_).
  {
    unfolds. unfolds state.
    auto.
  }
  lets H_: sdom_is_fn Hinv Hsd Hsd_.
  subst.
  unfolds in Hsdq.
  destruct Hsdq as [Heaq | Hefq].
  - unfolds in Heaq.
    simpljoin.
    uni_21_sym (get O quelsid).
    Set Printing Implicit.
    unfold Modules.qid in H0.
    uni_21 (get qls qid).
    Unset Printing Implicit.
    auto.
  - assert (Hsdq: q_sdom_ O qid td_).
    { unfolds. right. auto. }
    assert (Hsdq': q_sdom_ O qid tdq).
    {
      unfolds.
      left.
      unfolds. do 4 eexists; splits; eauto.
    }
    inverts Hinv.
    lets H_: inv_que_d_disj Hsdq Hsdq'.
    eauto.
Qed.

Lemma dte_ex_mq_in_dom_same:
  forall td O1 O2 qls1 qls2 q, 
    obsr_equiv_tskd td O1 O2 -> 
    get O1 quelsid = Some (absecblist qls1) -> 
    get O2 quelsid = Some (absecblist qls2) -> 
    (exists ms sz ts, get qls1 q = Some (msgq ms sz ts, td)) <->
      (exists ms sz ts, get qls2 q = Some (msgq ms sz ts, td)). 
Proof.
  introv Hoe Hg1 Hg2.
  inverts Hoe.
  eapply oe_td_mqs; eauto.
Qed.

Lemma dte_mq_cases:
  forall td O1 O2 a qls1 qls2, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 quelsid = Some (absecblist qls1) ->
    get O2 quelsid = Some (absecblist qls2) -> 
    match get qls1 a with 
      Some (msgq ms sz ts, td') =>
        (td' = td /\ get qls2 a = Some (msgq ms sz ts, td))
        \/
          (td' <> td /\
             match get qls2 a with
               Some (msgq _ _ _, td2') => td2' <> td
             | None => True
             end)
    | None => 
        match get qls2 a with
          Some (msgq _ _ _, td2') => td2' <> td
        | None => True
        end
    end.
Proof.
  introv Hdte Hg1 Hg2.
  unfolds in Hdte.
  inverts Hdte.
  unfolds in oe_td_mqs.
  destruct oe_td_mqs as (Heqv & Hall).
  clear Heqv.
  specialize (Hall qls1 qls2 a).
  specializes Hall; eauto.
  destruct Hall as (Hexeq & Hall).
  destruct (get qls1 a) eqn: E1.
  - destruct p as (q, td').
    destruct q as [ms sz ts].

    casetac td td' He Hne.
    + subst.
      assert (Hex: ex_mq_in_dom a td' qls1).
      {
        unfolds. do 3 eexists; eauto.
      }
      apply Hexeq in Hex.
      unfolds in Hex.
      destruct Hex as (ms2 & sz2 & ts2 & Hgq2).
      lets H__: Hall E1 Hgq2.
      specializes H__; eauto.
      inverts H__.
      left.
      split; auto.
    + right.
      split; auto.
      destruct (get qls2 a) eqn: E2.
      2: auto.
      destruct p as (q2, td2').
      destruct q2 as [ms2 sz2 ts2].
      casetac td2' td He Hf.
      ** subst.
         assert (Hex2: ex_mq_in_dom a td qls2).
         {
           unfolds. do 3 eexists; eauto.
         }
         apply Hexeq in Hex2.
         unfolds in Hex2.
         destruct Hex2 as (ms2_ & sz2_ & ts2_ & Hga).
         Set Printing Implicit.
         unfold tid in E1. unfold qid in Hga.
         rewrite E1 in Hga.
         Unset Printing Implicit.
         inverts Hga.
         auto.
      ** auto.
  -
    destruct (get qls2 a) eqn: E2.
    destruct p as (q2, td2').
    destruct q2 as [ms2 sz2 ts2].
    2: auto.
    casetac td2' td He Hf.
    ** subst.
       assert (Hex2: ex_mq_in_dom a td qls2).
       {
         unfolds. do 3 eexists; eauto.
       }
       apply Hexeq in Hex2.
       unfolds in Hex2.
       destruct Hex2 as (ms2_ & sz2_ & ts2_ & Hga).
       Set Printing Implicit.
       unfold tid in E1. unfold qid in Hga.
       rewrite E1 in Hga.
       Unset Printing Implicit.
       inverts Hga.
    ** auto.
Qed.

(* *)

Lemma dte_check_dom_prsv: 
  forall O1 O2 O1' O2' vl1' vl2' ac1 ac2 td td' vl t tp
         (Htvm : tl_vl_match (Tptr Tvoid :: tp :: nil) vl = true) 
         (Hpre11 : pre1 t O1 trivial_asrt)
         (Hpre12 : pre1 t O2 trivial_asrt)
         (Hdte : obsr_equiv_data (TaskDom td) O1 O2)
         (Hsd1 : sdom O1 t td')
         (Hsd2 : sdom O2 t td')
         (Hflt : flows_to (TaskDom td') (TaskDom td))
         (Hdte' : obsr_equiv_data (TaskDom td') O1 O2)
         (Hchkd1 : mq_check_dom t vl O1 ac1 (vl1', O1'))
         (Hchkd2 : mq_check_dom t vl O2 ac2 (vl2', O2')),  
         (* (Hntck1 : ~ (exists cid, ac1 = _TickAct cid)) *)
         (* (Hntck2 : ~ (exists cid, ac2 = _TickAct cid)),  *)
    obsr_equiv_data (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2'. 
Proof.
  intros.
  unfolds in Hchkd1; unfolds in Hchkd2.
  d_mt_hyp; simpl in Htvm; tryfalse.
  d_mt_hyp; simpl in Htvm; tryfalse.
  -
    inverts Hchkd1; inverts Hchkd2.
    simpljoin.
    split; auto.
  -
    destruct Hchkd1 as (tls1 & pr1 & st1 & msg1 & sus1 & td1 & qls1 & Hgtls1 & Hgt1 & Hgqls1 & Hmtq1).
    destruct Hchkd2 as (tls2 & pr2 & st2 & msg2 & sus2 & td2 & qls2 & Hgtls2 & Hgt2 & Hgqls2 & Hmtq2).
    assert (td1 = td').
    {
      lets H_: tls_sdom_td_eq Hpre11; eauto.
    }
    assert (td2 = td').
    {
      lets H_: tls_sdom_td_eq Hpre12; eauto.
    }
    subst td1 td2.
    lets H_: dte_mq_cases a Hdte' Hgqls1 Hgqls2.
    destruct (get qls1 a) eqn: E1.
    +
      destruct p as (q1 & td1).
      destruct q1 as [ms1 sz1 ts1].
      Set Printing Implicit.
      unfold tid in H_.
      rewrite E1 in H_.
      Unset Printing Implicit. 
      destruct Hmtq1; destruct H_; simpljoin; tryfalse.
      * rewrite H2 in Hmtq2.
        rn_or Hor1.
        destruct Hor1; destruct Hmtq2; simpljoin; tryfalse.
        split; auto.
        split; auto.
        rn_or Hor2.
        destruct Hor2; simpljoin; tryfalse.
      *
        rn_or Hor1.
        destruct Hor1; simpljoin; tryfalse.
        destruct (get qls2 a) eqn: E2.
        **
          destruct p as (q2 & td2).
          destruct q2 as [ms2 sz2 ts2].
          simpljoin; tryfalse.
          rn_or Hor2.
          destruct Hor2; simpljoin; tryfalse.
          splits; auto.
        **
          simpljoin; tryfalse.
          splits; eauto.
    +
      unfold tid in H_. rewrite E1 in H_.
      destruct (get qls2 a) eqn: E2.
      **
        destruct p as (q2 & td2).
        destruct q2 as [ms2 sz2 ts2].
        simpljoin; tryfalse.
        rn_or Hor2.
        destruct Hor2; simpljoin; tryfalse.
        splits; auto.
      **
        simpljoin; tryfalse.
        splits; eauto.
Qed.       

(*  *)

Lemma ex_prio_12: 
  forall td pr O1 O2 tls1 tls2, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) -> 
    (exists t' st msg0 sus, get tls1 t' = Some (pr, st, msg0, sus, td)) ->             
    (exists t' st msg0 sus, get tls2 t' = Some (pr, st, msg0, sus, td)).  
Proof.
  introv Hdte Hgtls1 Hgtls2 Hex1.
  -
    destruct Hex1 as (t & Hex1).
    assert (He: exists pr st msg0 sus, get tls1 t = Some (pr, st, msg0, sus, td)).
    {
      simpljoin. do 4 eexists; eauto.
    }
    lets H_: dte_ex_tsk_in_dom_same t Hdte Hgtls1 Hgtls2.
    eapply H_ in He.
    destruct He as (pr0 & st2 & m2 & su2 & Hgt2).
    clear H_.
    destruct Hex1 as (st1 & m1 & su1 & Hgt1).
    lets H_: obsr_equiv_data_tsk_eq Hdte Hgtls1 Hgtls2 Hgt1 Hgt2; eauto.
    simpljoin.
    do 4 eexists; eauto.
Qed.

Lemma ex_prio_eqv: 
  forall td pr O1 O2 tls1 tls2, 
    obsr_equiv_data (TaskDom td) O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) -> 
    ((exists t' st msg0 sus, get tls1 t' = Some (pr, st, msg0, sus, td)) <->             
       (exists t' st msg0 sus, get tls2 t' = Some (pr, st, msg0, sus, td))).
Proof.
  introv Hdte Hgtls1 Hgtls2.
  split.
  -
    introv Hex1.
    eapply ex_prio_12; eauto.
  -
    apply obsr_equiv_data_sym in Hdte.
    introv Hex2.
    eapply ex_prio_12; eauto.
Qed. 

Lemma ex_tsk_or:
  forall tls td i, 
    (exists t' st msg0 sus, get tls t' = Some (i, st, msg0, sus, td)) \/
      (~exists t' st msg0 sus, get tls t' = Some (i, st, msg0, sus, td)).
  intros.
  tauto.
Qed. 

