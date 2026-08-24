
Require Import LibTactics.
Require Import memory.
Require Import language. 
Require Import opsem.
Require Import rules.
Require Import my_tacs.

Require Import Coq.Logic.FunctionalExtensionality.

Section InversionLemmas.

Context {state_t : Type}.  
Context `{State state_t}.

Lemma ust_get_set_same: 
  forall (ust: ustate) d sst, 
    get ust d = Some sst ->
    set ust d sst = ust. 
Proof.
  introv Hg.
  apply map_eql.
  intro td.
  destruct (Int.eq_dec d td).
  ** subst d. rewrite map_get_set. auto.
  ** rewrite neq_set_get; eauto.
Qed. 

Lemma T_get_set_same: 
  forall (T: tasks) t C, 
    T t = Some C ->
    upd_task_pool T t C = T.
Proof.
  introv Hg.
  apply functional_extensionality.
  intros.
  casetac t x He Hne.
  - subst. rewrite upd_task_pool_eq; auto.
  - rewrite upd_task_pool_neq; eauto.
Qed. 

Lemma hpstep_d_tick_inversion:
  forall uprgs aspc ispc sd T ust O T' ust' O' cid d, 
    hpstep_d uprgs (aspc, ispc, sd) (T, ust, O) (T', ust', O') (TickAct cid) d ->
    exists t ks s s',
      (* valid_ct t O cid /\ *)
      cur_tsk O cid t /\ 
        spec_step sd t s O s' O' (_TickAct cid) /\
        T t = Some (cur_stmt s, ks) /\
        T' = upd_task_pool T t (cur_stmt s', ks) /\
        ust' = ust.  
Proof.
  introv Hstep.
  inverts Hstep.
  - 
    false.
    apply H12. eexists; eauto.
  -
    inv_hpstep.
    inv_htstep.
    + 
      destruct H8; simpljoin; tryfalse.
    +
      inv_hapistep.
      * 
        destruct H8; simpljoin; tryfalse.
      *
        destruct H8; simpljoin; tryfalse. inverts H8.
        destruct H12; simpljoin; tryfalse. inverts H0.
        simpl in H1.
        exists t ks cd cd'.
        splits; eauto.
        eapply ust_get_set_same; eauto.
      *
        destruct H8; simpljoin; tryfalse.
      *
        destruct H8; simpljoin; tryfalse.
Qed.

Lemma hpstep_d_sched_inversion:
  forall uprgs aspc ispc sd T ust O T' ust' O' cid d, 
    hpstep_d uprgs (aspc, ispc, sd) (T, ust, O) (T', ust', O') (SwAct cid) d ->
    exists t t' td asrt vs ks,
      (* get O coretid = Some (oscoret ct) /\ *)
      (* get ct cid = Some t /\ *)
      cur_tsk O cid t /\ 
        cur_dom O cid td /\ 
        (* sdom t O td /\ *)
        sd O td t' /\
        upd_cur_tsk O cid t' O' /\ 
        (* ct' = set ct cid t' /\ *)
        (* O' = set O coretid (oscoret ct') /\ *)
        ust' = ust /\
        T t = Some (cur_stmt (sched asrt;;> vs), ks) /\ 
        T' = upd_task_pool T t (cur_stmt (vs nil), ks). 
Proof.
  introv Hstp.
  inverts Hstp.
  - 
    false. apply H13; eexists; eauto.
  -
    destruct H12; inverts H0.
    inv_hpstep.
    + 
      destruct H8; simpljoin.
      inverts H1.
      inverts H1.
    +
      inv_tuple.
      do 6 eexists; splits; eauto.
Qed. 

Definition sched_act (ac: sec_act) :=
  match ac with
    TickAct cid | SwAct cid => True
  | _ => False
  end.

Lemma hpstep_inversion: 
  forall t uprgs aspc ispc sd T T' O O' ust ust' ac td,
    hpstep uprgs (aspc, ispc, sd) T ust O T' ust' O' (ac, t) -> 
    I O ->
    sdom O t td ->
    ~ (exists cid, ac = TickAct cid) -> 
    ~ (exists cid, ac = SwAct cid) -> 
    (
      (
        exists strat ks strat_ac sst sst' cid, 
          ac = TauAct cid /\ 
            T t = Some (cur_strat strat, ks) /\
            get ust td = Some sst /\ 
            strat sst Vundef = (strat_ac, sst') /\
            ~ (exists f vl, strat_ac = _CallAct f vl) /\
            T' = T /\
            ust' = set ust td sst' /\
            O' = O
      )
      \/
        (
          exists strat sst sst' f vl r tp tl cid, 
            ac = TauAct cid /\ 
              T t = Some (cur_strat strat, kstop) /\
              get ust td = Some sst /\ 
              strat sst Vundef = (_CallAct f vl, sst') /\
              aspc f = Some (r, (tp, tl)) /\
              tl_vl_match tl vl = true /\
              T' = upd_task_pool T t (cur_stmt (r vl), kenknl f strat kstop) /\
              ust' = set ust td sst' /\ 
              O' = O
        ) 
      \/
        (
          exists i c ks s cid,
            ac = EniAct cid i /\
              ispc i = Some s /\
              T t = Some (c, ks) /\
              T' = upd_task_pool T t (cur_stmt s, kevent i c ks) /\
              ust' = ust /\
              O' = O
        )
      \/
        (
          exists vl f strat ks ac_strat sst sst' cid, 
            ac = TauAct cid /\ 
              T t = Some (cur_stmt (spec_done vl), kenknl f strat ks) /\
              get ust td = Some sst /\
              strat sst (match vl with | nil => Vundef | v :: _ => v end) = (ac_strat, sst') /\  
              T' = upd_task_pool T t (cur_strat strat, ks) /\
              ust' = set ust td sst' /\
              O' = O 
        )
      \/
        (
          exists i c ks cid, 
            ac = TauAct cid /\ 
              T t = Some (cur_stmt (spec_done nil), kevent i c ks) /\
              T' = upd_task_pool T t (c, ks) /\
              ust' = ust /\
              O' = O 
        )
      \/
        (exists s ks s' ac_ cid,
            ac = TauAct cid /\ 
              T t = Some (cur_stmt s, ks) /\
              spec_step sd t s O s' O' ac_ /\
              (~exists cid, ac_ = _TickAct cid) /\
              (
                ((~exists t' f arg, ac_ = _TCreAct t' f arg) /\
                   T' = upd_task_pool T t (cur_stmt s', ks))
                \/
                  (exists t' f arg valstr strat,
                      ac_ = _TCreAct t' f arg /\ get uprgs f = Some valstr /\ valstr (Vptr arg) = strat /\
                        T' = upd_task_pool (upd_task_pool T t (cur_stmt s', ks)) t' (cur_strat strat, kstop))
              ) /\ 
              ust' = ust 
        )
    ).  
Proof.
  introv Hstep Hinv Hsdom Hntck Hnswi.
  assert (Hdom : forall d, sdom O t d -> td = d).
  {
    intros d_ Hd.
    lets H_: sdom_is_fn Hinv; eauto.
  }
  inverts Hstep.

  - (* htstep *)
    rn_or Hact_or.
    destruct Hact_or as [Htck | Hntck_].
    destruct Htck as (Hsema & Hseca).
    subst ac. false. apply Hntck; eexists; eauto.
    destruct Hntck_ as (Hsema & Hseca); subst.
    inv_htstep.
    + (* user step *) 
      specialize (Hdom _ H3).
      subst.
      left.
      do 6 eexists; splits; eauto.
      eapply T_get_set_same; eauto.
    + (* api step *)
      inv_hapistep.
      * (* entrance to API *)
        inv_tuple.
        destruct Hsema; simpljoin; try discriminate.
        inverts H0.        
        specialize (Hdom _ H3). subst. 
        right; left.
        do 9 eexists; splits; eauto.
      * (* spec_step *)
        destruct Hsema; simpljoin; subst.
        ** 
          specialize (Hdom _ H3). subst.
          right; right; right; right; right.
          do 5 eexists; splits; eauto.
          introv Hf; simpljoin; tryfalse.
          eapply ust_get_set_same; eauto.
        **
          false; apply H5.
          do 2 eexists; eauto.
      *
        specialize (Hdom _ H3). subst.
        right; right; right.
        left.
        do 8 eexists; splits; eauto.
      *
        specialize (Hdom _ H3). subst.
        right; right; right; right.
        left.
        do 4 eexists; splits; eauto.
        eapply ust_get_set_same; eauto.

  - (* htistep *)
    inv_tuple.
    inv_htistep.
    right; right. left.
    do 5 eexists; splits; eauto.
    
  - (* sched step *)
    false. apply Hnswi. eexists; eauto.

  - (* task creation step *)
    inv_htstep.
    inv_hapistep.
    right; right; right; right; right.
    do 5 eexists; splits; eauto.
    introv Hf; simpljoin; tryfalse.
    right.
    do 5 eexists; splits; eauto.

  - (* task deletion step *)
    inv_htstep.
    inv_hapistep.
    right; right; right; right; right.
    do 5 eexists; splits; eauto.
    introv Hf; simpljoin; tryfalse.
    left.
    split.
    + introv Hf; simpljoin; tryfalse.
    + auto.
Qed. 

Lemma hpstep2_inversion:
  forall t uprgs aspc ispc sd T1 T2 T1' T2' O1 O2 O1' O2' ust1 ust2 ust1' ust2' ac td,
    hpstep uprgs (aspc, ispc, sd) T1 ust1 O1 T1' ust1' O1' (ac, t) -> 
    hpstep uprgs (aspc, ispc, sd) T2 ust2 O2 T2' ust2' O2' (ac, t) -> 
    T1 t = T2 t -> 
    I O1 ->
    I O2 -> 
    sdom O1 t td ->
    sdom O2 t td ->
    get ust1 td = get ust2 td ->  
    ~ sched_act ac -> 
    (
      (
        exists strat ks strat_ac sst sst' cid, 
          ac = TauAct cid /\ 
            T1 t = Some (cur_strat strat, ks) /\
            (* get T2 t = Some (cur_strat strat, ks) /\ *)
            get ust1 td = Some sst /\ 
            strat sst Vundef = (strat_ac, sst') /\
            ~ (exists f vl, strat_ac = _CallAct f vl) /\
            T1' = T1 /\
            T2' = T2 /\ 
            ust1' = set ust1 td sst' /\
            ust2' = set ust2 td sst' /\
            O1' = O1 /\
            O2' = O2
      )
      \/
        (
          exists strat sst sst' f vl r tp tl cid, 
            ac = TauAct cid /\ 
              T1 t = Some (cur_strat strat, kstop) /\
              (* get T2 t =  Some (cur_strat strat, kstop) /\ *) 
              get ust1 td = Some sst /\ 
              strat sst Vundef = (_CallAct f vl, sst') /\
              aspc f = Some (r, (tp, tl)) /\
              tl_vl_match tl vl = true /\
              T1' = upd_task_pool T1 t (cur_stmt (r vl), kenknl f strat kstop) /\
              T2' = upd_task_pool T2 t (cur_stmt (r vl), kenknl f strat kstop) /\
              ust1' = set ust1 td sst' /\
              ust2' = set ust2 td sst' /\
              O1' = O1 /\
              O2' = O2
        )
      \/
        (
          exists i c ks s cid,
            ac = EniAct cid i /\
              ispc i = Some s /\
              T1 t = Some (c, ks) /\
              T1' = upd_task_pool T1 t (cur_stmt s, kevent i c ks) /\
              T2' = upd_task_pool T2 t (cur_stmt s, kevent i c ks) /\  
              ust1' = ust1 /\
              ust2' = ust2 /\ 
              O1' = O1 /\
              O2' = O2 
        )
      \/
        (
          exists vl f strat ks ac_strat sst sst' cid, 
            ac = TauAct cid /\ 
              T1 t = Some (cur_stmt (spec_done vl), kenknl f strat ks) /\
              get ust1 td = Some sst /\
              strat sst (match vl with | nil => Vundef | v :: _ => v end) = (ac_strat, sst') /\  
              T1' = upd_task_pool T1 t (cur_strat strat, ks) /\
              T2' = upd_task_pool T2 t (cur_strat strat, ks) /\
              ust1' = set ust1 td sst' /\
              ust2' = set ust2 td sst' /\
              O1' = O1 /\
              O2' = O2
        )
      \/
        (
          exists i c ks cid, 
            ac = TauAct cid /\ 
              T1 t = Some (cur_stmt (spec_done nil), kevent i c ks) /\
              T1' = upd_task_pool T1 t (c, ks) /\
              T2' = upd_task_pool T2 t (c, ks) /\
              ust1' = ust1 /\
              ust2' = ust2 /\
              O1' = O1 /\
              O2' = O2
        )
      \/
        (exists s ks s1' s2' ac1 ac2 cid,
            ac = TauAct cid /\ 
              T1 t = Some (cur_stmt s, ks) /\
              spec_step sd t s O1 s1' O1' ac1 /\
              spec_step sd t s O2 s2' O2' ac2 /\
              (~exists cid, ac1 = _TickAct cid) /\
              (~exists cid, ac2 = _TickAct cid) /\ 
              (
                ((~exists t' f arg, ac1 = _TCreAct t' f arg) /\
                   T1' = upd_task_pool T1 t (cur_stmt s1', ks))
                \/
                  (exists t' f arg valstr strat,
                      ac1 = _TCreAct t' f arg /\ get uprgs f = Some valstr /\ valstr (Vptr arg) = strat /\
                        T1' = upd_task_pool (upd_task_pool T1 t (cur_stmt s1', ks)) t' (cur_strat strat, kstop))
              ) /\ 
              (
                ((~exists t' f arg, ac2 = _TCreAct t' f arg) /\
                   T2' = upd_task_pool T2 t (cur_stmt s2', ks))
                \/
                  (exists t' f arg valstr strat, 
                      ac2 = _TCreAct t' f arg /\ get uprgs f = Some valstr /\ valstr (Vptr arg) = strat /\
                        T2' = upd_task_pool (upd_task_pool T2 t (cur_stmt s2', ks)) t' (cur_strat strat, kstop) 
                  )
              ) /\ 
              ust1' = ust1 /\ 
              ust2' = ust2
        )
    ).  
Proof.    
  introv (* Hgup *) Hstep1 Hstep2 HgTeq Hinv1 Hinv2 Hsd1 Hsd2 Husteq.
  introv Hnscha.
  inverts Hstep1.

  assert (Hdom1 : forall d, sdom O1 t d -> td = d).
  {
    intros d_ Hd.
    lets H_: sdom_is_fn Hinv1; eauto.
  }
  assert (Hdom2 : forall d, sdom O2 t d -> td = d).
  {
    intros d_ Hd.
    lets H_: sdom_is_fn Hinv2; eauto.
  }
  
  - (* left step is normal htstep (not task creation/deletion) *) 
    match goal with H: _ \/ _ |- _ => rename H into H_act_or end.
    destruct H_act_or as [Htck | Hntck1].
    destruct Htck as (Hsema & Hseca).
    subst ac. false. apply Hnscha. 
    unfolds. auto.
    destruct Hntck1 as (H_act1 & Hac1).
    subst.
    inv_htstep. (* left step *)

    + (* left step is user step *)
      rewrite H17 in HgTeq.
      symmetry in HgTeq.
      inverts Hstep2.

      * (* right step is normal htstep *) 
        match goal with H: _ \/ _ |- _ => rename H into H_act_or end.
        destruct H_act_or as [Htck | Hntck2].
        simpljoin; tryfalse. 
        destruct Hntck2 as (H_act2 & Hac2).
        inverts Hac2.
        destruct H_act2; simpljoin; subst.
        2: {
          inv_htstep. (* right *)
          inv_hapistep.
          - 
            asst_same_code12 T2 t.
            assert (td = d) by (eapply Hdom1;eauto).
            assert (td = d0) by (eapply Hdom2;eauto).
            subst. 
            inverts HC.
            Set Printing Implicit.
            unfold ustratstate.B in Husteq.
            rewrite H4 in Husteq.
            rewrite H11 in Husteq.
            inverts Husteq.
            Unset Printing Implicit.
            rewrite H1 in H18; inverts H18. (* strat1 sst0 Vundef *)
            false; apply H8; eexists; eauto.
          -
            false; apply H12; do 2 eexists; eauto.
        }

        inv_htstep. (* right *)
        ** (* right step is user step *) 
          match goal with
            HgTeq: context [T2 t],
              H: context [T2 t] |- _ =>
              rewrite H in HgTeq; inverts HgTeq 
          end.
          assert (td = d) by (lets H_: Hdom1 H3; eauto).
          subst d.
          assert (td = d0) by (lets H_: Hdom2 H10; eauto). 
          subst d0.
          Set Printing Implicit.
          unfold ustratstate.B in Husteq.
          asst_same_ust ust1 ust2 td Husteq.
          Unset Printing Implicit.
          left.
          do 6 eexists; splits; eauto.
          apply T_get_set_same; auto.
          apply T_get_set_same; auto.
          splits; eauto.
          congruence. 
        ** (*  *)
          rewrite H25 in HgTeq.
          inverts HgTeq.
          inv_hapistep.

      * (* right step is htstep for task creation *)
        rewrite H10 in HgTeq; inverts HgTeq.
        inv_htstep. (* right step *)
        inv_hapistep. (* right step *) 

      * (* right step is htstep for task deletion *)
        rewrite H10 in HgTeq; inverts HgTeq.
        inv_htstep. (* right step *)
        inv_hapistep. (* right step *) 

    + (* left step is API step *)
      destruct H_act1 as [Htau_ac | Hcall_ac]; simpljoin; subst.
      2: {
        inv_hapistep. 

        - (* left step is call to API *) 
          inv_tuple.
          
          inv_hpstep. (* right step *)
          +
            asst_same_code T1 T2 t HgTeq.
            subst C.
            assert (td = d) by (eapply Hdom1; eauto).
            subst d.
            assert (td = d0) by (eapply Hdom2; eauto). 
            subst d0.
            Set Printing Implicit.
            unfold ustratstate.B in Husteq.
            asst_same_ust ust1 ust2 td Husteq.
            Unset Printing Implicit.
            rn_or Hact_or.
            destruct Hact_or as [Htcka | Hntcka].
            simpljoin; tryfalse.
            destruct Hntcka as (Hsema & Hseca); inverts Hseca.
            destruct Hsema; simpljoin; subst.
            * (* right step is htstep with _TauAct *)
              inv_htstep.
              ** 
                subst. inverts H0.
                rewrite H1 in H10; inverts H10.
                false; apply H15; eauto.
              **
                inv_hapistep.
            * (* right step is htstep with _CallAct *)
              inv_htstep. (* right *)
              inv_hapistep.
              inv_tuple.
              inv_tuple.
              rewrite H10 in H18; inverts H18.
              rewrite H11 in H19; inverts H19.
              right. left.
              do 9 eexists; splits; eauto.
          + (* right step is task creation step *)
            asst_same_code T1 T2 t HgTeq.
            subst C.
            inv_htstep. (* right *)
            inv_hapistep. (* right *)
          + (* right step is tack deletion step *)
            asst_same_code T1 T2 t HgTeq.
            subst C.
            inv_htstep. (* right *)
            inv_hapistep. (* right *)

        - (*  *)
          false; apply H5; do 2 eexists; eauto.
      }
        
      inv_hapistep. (* left step *) 
      * (* left step is spec_step *)
        inv_hpstep. (* right step *)  
        ** (* right step is ordinary htstep (not task creation/deletion) *)  
          rn_or H_act_or.
          destruct H_act_or as [Htck | Hntck2].
          simpljoin; tryfalse. 
          destruct Hntck2 as (H_act2 & Hac2).
          inverts Hac2.
          asst_same_code T1 T2 t HgTeq.
          subst C.
          destruct H_act2 as [Htau_act | Hcall_act]; simpljoin; subst.
          2: {
            inv_htstep.
            inv_hapistep.
            inv_tuple.
            false; apply H26; do 2 eexists; eauto.
          }
          
          inv_htstep. (* right *)
          ***
            inv_tuple.
          ***
            inv_hapistep. (* right *)
            **** (* right step is spec_step *) 
              right; right; right; right; right.
              do 7 eexists; splits; eauto.
              introv Hf; simpljoin; tryfalse.
              introv Hf; simpljoin; tryfalse.
              splits; eauto.
              eapply ust_get_set_same; eauto.
              eapply ust_get_set_same; eauto.
            **** (* right step is exiting from API *) 
              inv_specstep. (* left step *)
            ****
              inv_specstep.
        ** (* right step is task creation step *)
          inv_htstep. (* right *)
          inv_hapistep.
          asst_same_code T1 T2 t HgTeq.
          inverts HC.
          right; right; right; right; right.
          do 7 eexists; splits; eauto.
          introv Hf; simpljoin; tryfalse. 
          introv Hf; simpljoin; tryfalse.
          splits; eauto.
          right.
          do 5 eexists; splits; eauto.
          eapply ust_get_set_same; eauto.
        ** (* right step is task deletion step *)
          inv_htstep. (* right *)
          inv_hapistep.
          asst_same_code T1 T2 t HgTeq.
          inverts HC.
          right; right; right; right; right.
          do 7 eexists; splits; eauto.
          introv Hf; simpljoin; tryfalse.
          introv Hf; simpljoin; tryfalse.
          splits; eauto.
          left. 
          split. introv Hf; simpljoin. inverts H0. auto.
          eapply ust_get_set_same; eauto.

      * (* left step is exit from API *)
        inv_hpstep. (* right *)
        ** (* right step is htstep *)
          rn_or H_act_or.
          destruct H_act_or as [Htck | Hntck].
          simpljoin; tryfalse.
          destruct Hntck as (H_act & Htau_acteq).
          inverts Htau_acteq.
          asst_same_code T1 T2 t HgTeq.
          subst C.
          
          destruct H_act; simpljoin; subst.
          2: {
            inv_htstep.
            inv_hapistep.
            inv_tuple.
            false; apply H25; eauto.
          }
          
          inv_htstep. (* right *)
          *** (* right step is user step *)
            inv_tuple. 
          *** (* right step is API step *)
            inv_hapistep.  (* right *)
            **** (* right step is spec_step *)
              inv_specstep. (* right *)
            **** (* right step is exit from API *)
              assert (td = d) by (eapply Hdom1; eauto). 
              subst d.
              assert (td = d0) by (eapply Hdom2; eauto). 
              subst d0.
              unfold ustratstate.B in Husteq.              
              asst_same_ust ust1 ust2 td Husteq.              
              subst sst.
              right. right. right. left.
              do 8 eexists; splits; eauto.
              rewrite H1 in H25. (*strat0 sst0 match ... *)
              inv_tuple.
              auto.
        ** (* right step is task creation step *)
          asst_same_code T1 T2 t HgTeq.
          subst C.
          inv_htstep. (* right. *)
          inv_hapistep. (* right *)
          inv_specstep. (* right *) 
        ** (* right step is task deletion step *) 
          asst_same_code T1 T2 t HgTeq.
          subst C.
          inv_htstep. (* right. *)
          inv_hapistep. (* right *)
          inv_specstep. (* right *) 

      * (* left step is exit from interrupt handler *)
        inv_hpstep. (* right *)
        ** (* right step is htstep *)
          rn_or H_act_or.
          destruct H_act_or as [Htck | Hntck].
          simpljoin; tryfalse.
          destruct Hntck as (H_act & Haceq).
          inverts Haceq.
          asst_same_code T1 T2 t HgTeq.
          subst C.

          destruct H_act; simpljoin; subst.
          2: {
            inv_htstep.
            inv_hapistep.
            inv_tuple.
            false; apply H24; eauto.
          }
          
          inv_htstep. (* right *)
          *** (* right step is user step *)
            inv_tuple. 
          *** (* right step is API step *)
            inv_hapistep.  (* right *)
            **** (* right step is spec_step *)
              inv_specstep. (* right *)
            **** (* right step is exit from interrupt handler *)
              assert (td = d) by (eapply Hdom1; eauto).
              subst d.
              assert (td = d0) by (eapply Hdom2; eauto). 
              subst d0.
              unfold ustratstate.B in Husteq.                      
              asst_same_ust ust1 ust2 td Husteq.              
              subst sst'.
              right. right. right. right. left. 
              do 4 eexists; splits; eauto.
              eapply ust_get_set_same; eauto.          
              eapply ust_get_set_same; eauto.      
        ** (* right step is task creation step *)
          asst_same_code T1 T2 t HgTeq.
          subst C.
          inv_htstep. (* right. *)
          inv_hapistep. (* right *)
          inv_specstep. (* right *) 
        ** (* right step is task deletion step *) 
          asst_same_code T1 T2 t HgTeq.
          subst C.
          inv_htstep. (* right. *)
          inv_hapistep. (* right *)
          inv_specstep. (* right *) 

  - (* left step is htistep *)
    inv_tuple.
    inv_htistep. (* left *)
    inv_hpstep. (* right *)
    + (* right step is htstep *)
      rn_or H_act_or.
      destruct H_act_or as [Htck | Hntck]; simpljoin; tryfalse.
    + (* right step is htistep *)
      inv_htistep. (* right *)
      inv_tuple.
      match goal with
        Hi1: ispec0 i = Some ?l0, Hi2: ispec0 i = Some ?l1 |- _ =>
          rewrite Hi1 in Hi2; inverts Hi2
      end.
      asst_same_code T1 T2 t HgTeq.
      inverts HC.
      right. right. left.
      do 5 eexists; splits; eauto.

  - (* left step is context switch *) 
    false; apply Hnscha.
    unfolds. auto.

  - (* left step is task creation step *)
    inv_htstep.  (* left *)
    inv_hapistep. (* left *)
    inv_hpstep. (* right *)
    * (* right step is htstep *)
      rn_or H_act_or.
      destruct H_act_or as [Htck | Hntck].
      destruct Htck; subst; tryfalse.
      destruct Hntck as (Hor & Htaueq).
      inverts Htaueq.
      asst_same_code T1 T2 t HgTeq.
      subst C.
      destruct Hor; simpljoin; subst.

      2: {
        inv_htstep.
        inv_hapistep.
        inv_tuple.
        false; apply H24; eauto.
      }
            
      inv_htstep. (* right *)
      ** (* right step is user step *)
        inv_tuple.
      ** (* right step is API step *) 
        inv_hapistep.
        *** (* right step is spec_step *)
          right. right. right. right. right.
          do 7 eexists; splits; eauto.
          introv Hf; simpljoin; tryfalse.
          introv Hf; simpljoin; tryfalse.
          right.
          do 5 eexists; splits; eauto.
          splits; eauto.
          eapply ust_get_set_same; eauto.
        *** (* right step is exit from API *)
          inv_specstep. (* left *)
        *** (* right step is exit from interrupt handler *)
          inv_specstep. (* left *)
    * (* right step is task creation step *) 
      inv_htstep. (* right *)
      asst_same_code T1 T2 t HgTeq.
      subst C.
      inv_hapistep. (* right *)
      right. right. right. right. right.
      do 7 eexists; splits; eauto.
      introv Hf; simpljoin; tryfalse.
      introv Hf; simpljoin; tryfalse.
      right.
      do 5 eexists; splits; eauto.
      splits; eauto.
      right.
      do 5 eexists; splits; eauto.
    * (* right step is task deletion step *)      
      inv_htstep. (* right *)
      asst_same_code T1 T2 t HgTeq.
      subst C.
      inv_hapistep. (* right *)
      right. right. right. right. right.
      do 7 eexists; splits; eauto.
      introv Hf; simpljoin; tryfalse.
      introv Hf; simpljoin; tryfalse.
      right.
      do 5 eexists; splits; eauto.
      splits; eauto.
      left. split. introv Hf; simpljoin; tryfalse.
      auto.

  - (* left step is task deletion step *)
    inv_htstep.  (* left *)
    inv_hapistep. (* left *)
    inv_hpstep. (* right *)
    * (* right step is htstep *)
      rn_or H_act_or.
      destruct H_act_or as [Htck | Hntck]. 
      destruct Htck; subst; tryfalse.
      destruct Hntck as (Hor & Htaueq).
      inverts Htaueq.
      asst_same_code T1 T2 t HgTeq.
      subst C.
      destruct Hor; simpljoin; subst.      

      2: {
        inv_htstep.
        inv_hapistep.
        inv_tuple.
        false; apply H23; eauto.
      }
      
      inv_htstep. (* right *)
      ** (* right step is user step *)
        inv_tuple.
      ** (* right step is API step *) 
        inv_hapistep.
        *** (* right step is spec_step *)
          right. right. right. right. right.
          do 7 eexists; splits; eauto.
          introv Hf; simpljoin; tryfalse.
          introv Hf; simpljoin; tryfalse.
          left. 
          split. introv Hf; simpljoin; tryfalse.
          auto.
          splits; eauto.
          eapply ust_get_set_same; eauto.
        *** (* right step is exit from API *)
          inv_specstep. (* left *)
        *** (* right step is exit from interrupt handler *)
          inv_specstep. (* left *)
    * (* right step is task creation step *) 
      inv_htstep. (* right *)
      asst_same_code T1 T2 t HgTeq.
      subst C.
      inv_hapistep. (* right *)
      right. right. right. right. right.
      do 7 eexists; splits; eauto.
      introv Hf; simpljoin; tryfalse.
      introv Hf; simpljoin; tryfalse.      
      left. split. introv Hf; simpljoin; tryfalse. 
      auto.
      splits; eauto.
      right.
      do 5 eexists; splits; eauto.
    * (* right step is task deletion step *)      
      inv_htstep. (* right *)
      asst_same_code T1 T2 t HgTeq.
      subst C.
      inv_hapistep. (* right *)
      right. right. right. right. right.
      do 7 eexists; splits; eauto.
      introv Hf; simpljoin; tryfalse.
      introv Hf; simpljoin; tryfalse.
      left. split. introv Hf; simpljoin; tryfalse.
      auto.
      splits; eauto.
      left. split. introv Hf; simpljoin; tryfalse.
      auto.
Qed.     

End InversionLemmas.
