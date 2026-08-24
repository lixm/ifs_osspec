
Require Import memory. 
Require Import language.
Require Import my_tacs.

Set Implicit Arguments.
Unset Strict Implicit.


Inductive absdataid:=
| abstcblsid: absdataid
| quelsid: absdataid
| chlsid: absdataid
| freetid: absdataid
| freeqid: absdataid
(* | ufuncsid: absdataid *) 
| ostmid: absdataid
| coretid: absdataid   
(* | curtid:absdataid *)
(* | tskctrlstid: absdataid *)
| dschedidxid: absdataid (* KsDomScheduleIdx *) 
| dschedlenid: absdataid (* KsDomScheduleLength *)
| curdomid: absdataid (* KsCurDomain *)
| lastdomid: absdataid (* KsLastDomain *)
| domtimeid: absdataid (* KsDomainTime *)
| dschedid: absdataid (* KsDomSchedule[idx] *) 
.

Definition absdataid_eq (id1 id2:absdataid):=
  match id1, id2 with
  | abstcblsid, abstcblsid => true
  | quelsid,quelsid => true
  | chlsid, chlsid => true
  | freetid, freetid => true
  | freeqid, freeqid => true 
  | ostmid, ostmid => true
  | coretid, coretid => true
  (* | curtid,curtid => true *)
  (* | tskctrlstid, tskctrlstid => true  *)
  | dschedidxid, dschedidxid => true
  | dschedlenid, dschedlenid => true
  | curdomid, curdomid => true
  | lastdomid, lastdomid => true
  | domtimeid, domtimeid => true
  | dschedid, dschedid => true
  | _,_ => false
  end.

Definition absdataid_lt (id1 id2:absdataid):=
  match id1, id2 with
  | abstcblsid, abstcblsid => false
  | abstcblsid, _ => true

  | quelsid, abstcblsid => false
  | quelsid, quelsid => false
  | quelsid, _ =>true

  | chlsid, abstcblsid => false 
  | chlsid, quelsid => false
  | chlsid, chlsid => false
  | chlsid, _ => true

  | freetid, abstcblsid => false
  | freetid, quelsid => false
  | freetid, chlsid => false
  | freetid, freetid => false
  | freetid, _ => true
    
  | freeqid, abstcblsid => false
  | freeqid, quelsid => false
  | freeqid, chlsid => false
  | freeqid, freetid => false
  | freeqid, freeqid => false
  | freeqid, _ => true 
    
  | ostmid, abstcblsid =>false
  | ostmid, quelsid => false
  | ostmid, chlsid => false
  | ostmid, freetid => false
  | ostmid, freeqid => false 
  | ostmid, ostmid => false
  | ostmid, _ => true

  | coretid, abstcblsid => false
  | coretid, quelsid => false
  | coretid, chlsid => false
  | coretid, freetid => false
  | coretid, freeqid => false 
  | coretid, ostmid => false
  | coretid, coretid => false
  | coretid, _ => true

  (* | tskctrlstid, abstcblsid => false  *)
  (* | tskctrlstid, quelsid => false *)
  (* | tskctrlstid, chlsid => false *)
  (* | tskctrlstid, freetid => false *)
  (* | tskctrlstid, freeqid => false *)
  (* | tskctrlstid, ostmid => false *)
  (* | tskctrlstid, coretid => false *)
  (* | tskctrlstid, tskctrlstid => false *)
  (* | tskctrlstid, _ => true *)

  | dschedidxid, abstcblsid => false 
  | dschedidxid, quelsid => false 
  | dschedidxid, chlsid => false 
  | dschedidxid, freetid => false
  | dschedidxid, freeqid => false  
  | dschedidxid, ostmid => false 
  | dschedidxid, coretid => false 
  (* | dschedidxid, tskctrlstid => false *)
  | dschedidxid, dschedidxid => false
  | dschedidxid, _ => true

  | dschedlenid, abstcblsid => false 
  | dschedlenid, quelsid => false 
  | dschedlenid, chlsid => false
  | dschedlenid, freetid => false
  | dschedlenid, freeqid => false  
  | dschedlenid, ostmid => false 
  | dschedlenid, coretid => false 
  (* | dschedlenid, tskctrlstid => false *)
  | dschedlenid, dschedidxid => false
  | dschedlenid, dschedlenid => false
  | dschedlenid, _ => true

  | curdomid, abstcblsid => false 
  | curdomid, quelsid => false 
  | curdomid, chlsid => false
  | curdomid, freetid => false
  | curdomid, freeqid => false  
  | curdomid, ostmid => false 
  | curdomid, coretid => false 
  (* | curdomid, tskctrlstid => false *)
  | curdomid, dschedidxid => false
  | curdomid, dschedlenid => false
  | curdomid, curdomid => false
  | curdomid, _ => true

  | lastdomid, abstcblsid => false 
  | lastdomid, quelsid => false 
  | lastdomid, chlsid => false
  | lastdomid, freetid => false
  | lastdomid, freeqid => false  
  | lastdomid, ostmid => false 
  | lastdomid, coretid => false 
  (* | lastdomid, tskctrlstid => false *)
  | lastdomid, dschedidxid => false
  | lastdomid, dschedlenid => false
  | lastdomid, curdomid => false
  | lastdomid, lastdomid => false
  | lastdomid, _ => true

  | domtimeid, abstcblsid => false 
  | domtimeid, quelsid => false 
  | domtimeid, chlsid => false
  | domtimeid, freetid => false
  | domtimeid, freeqid => false
  | domtimeid, ostmid => false 
  | domtimeid, coretid => false 
  (* | domtimeid, tskctrlstid => false *)
  | domtimeid, dschedidxid => false
  | domtimeid, dschedlenid => false
  | domtimeid, curdomid => false
  | domtimeid, lastdomid => false
  | domtimeid, domtimeid => false
  | domtimeid, _ => true
                        
  | dschedid, abstcblsid => false 
  | dschedid, quelsid => false 
  | dschedid, chlsid => false 
  | dschedid, freetid => false
  | dschedid, freeqid => false     
  | dschedid, ostmid => false 
  | dschedid, coretid => false 
  (* | dschedid, tskctrlstid => false *)
  | dschedid, dschedidxid => false
  | dschedid, dschedlenid => false
  | dschedid, curdomid => false
  | dschedid, lastdomid => false
  | dschedid, domtimeid => false
  | dschedid, dschedid => false
  end.

Module absdataidspec.
  Definition A := absdataid.
  Definition beq := absdataid_eq.
  Definition blt := absdataid_lt.
  
  Lemma beq_true_eq : forall a a' : A,
      beq a a' = true -> a = a'.
  Proof.
    intros.
    destruct a,a';simpl in H;auto;tryfalse.
  Qed.    

  Lemma beq_false_neq : forall a a' : A,
      beq a a' = false -> a <> a'.
  Proof. 
    intros.
    destruct a,a';simpl in H; introv Hf; auto;tryfalse.
  Qed.  

  Lemma eq_beq_true : forall a a' : A,
      a = a' -> beq a a' = true.
  Proof.
    intros.
    destruct a,a';simpl in H;auto;tryfalse.
  Qed.

  Lemma neq_beq_false : forall a a' : A,
      a <> a' -> beq a a' = false.
  Proof.
    intros.
    destruct a ,a';simpl in H;auto;tryfalse.
  Qed.

  Lemma blt_trans : 
    forall a a' a'' : A,
      blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
  Proof.
    unfold blt; intros.
    destruct a,a',a'';simpl in H, H0;auto;tryfalse.
  Qed.

  Lemma blt_irrefl :
    forall a : A,
      blt a a = false.
  Proof.  
    unfold blt; intros.
    destruct a;simpl;auto.
  Qed.

  Lemma blt_asym : 
    forall a b : A, 
      blt a b = true -> blt b a = false.
  Proof.  
    unfold blt; intros.
    destruct a,b;simpl in *;auto;tryfalse.
  Qed.

  Lemma blt_beq_dec :
    forall a b : A,
      {blt a b = true} + {beq a b = true} + {blt b a = true}.
  Proof.
    unfold blt; unfold beq; intros.
    remember (absdataid_lt a b) as bool1; destruct bool1.
    left; left; auto.
    remember (absdataid_eq a b) as bool2; destruct bool2.
    left; right; auto.
    destruct a,b;simpl in *;auto;tryfalse.
  Qed.  

End absdataidspec.

Definition priority := int32.
Definition msg := val.
Definition chmsg := val.
Definition maxlen := int32.
Definition ostime := int32.

Definition chid := nat. 

Inductive tcbstats:=
| os_stat_qpend: qid -> tcbstats. 
(* | os_stat_chpend: chid -> tcbstats.   *)

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> option int32 -> taskstatus.
(* "wait (os_stat_x eid) (Some t)" or "wait (os_stat_x eid) None" *)

Definition sus_st := bool. 


Module abstcb.
  Definition B : Set := (priority * taskstatus * msg * (* chmsg *  *)sus_st * task_dom)%type. 
  Definition holder : B := (Int.zero, rdy, Vnull, (* Vnull,  *)false, Int.mone). 
End abstcb.

Module TcbMod := MapLib.MapFun tidspec abstcb.

Program Instance TcbMap:
  PermMap tid (priority * taskstatus * msg * (* chmsg * *) sus_st * task_dom) TcbMod.map := 
  {
    usePerm := TcbMod.usePerm;
    isRw := TcbMod.isRw;
    flip := TcbMod.flip;
    sameV := TcbMod.sameV;
    same := TcbMod.same;
    emp := TcbMod.emp;
    join := TcbMod.join;
    del := TcbMod.del;
    get := TcbMod.get;
    set := TcbMod.set;
    sig := TcbMod.sig;
    merge := TcbMod.merge;
    minus := TcbMod.minus;
    map_dec_a := TcbMod.map_dec_a
}.
Next Obligation.
  apply TcbMod.map_join_emp.
Qed.
Next Obligation.
  apply TcbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_eql; auto.
Qed.
Next Obligation.
  apply TcbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_get_sig.
Qed.
Next Obligation.
  apply TcbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TcbMod.map_get_set.
Qed.
Next Obligation.
  apply TcbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_set_emp.
Qed.
Next Obligation.
  apply TcbMod.map_set_sig.
Qed.
Next Obligation.
  apply TcbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TcbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_del_sem.
Qed.

(* Definition owner:= option (tid * int32). *)

Inductive qdata := 
| msgq : list msg -> maxlen -> list tid -> qdata. 

Module msgque.
  Definition B : Set := prod qdata task_dom. 
  Definition holder : B := (msgq nil Int.zero nil, Int.mone).
End msgque.

Module QueMod := MapLib.MapFun qidspec msgque.

Program Instance QueMap: PermMap tid (prod qdata task_dom) QueMod.map :=
  {
    usePerm := QueMod.usePerm;
    isRw := QueMod.isRw;
    flip := QueMod.flip;
    sameV := QueMod.sameV;
    same := QueMod.same;
    emp := QueMod.emp;
    join := QueMod.join;
    del := QueMod.del;
    get := QueMod.get;
    set := QueMod.set;
    sig := QueMod.sig;
    merge := QueMod.merge;
    minus := QueMod.minus;
    map_dec_a := QueMod.map_dec_a
  }.
Next Obligation.
  apply QueMod.map_join_emp.
Qed.
Next Obligation.
  apply QueMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply QueMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply QueMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply QueMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply QueMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply QueMod.map_eql; auto.
Qed.
Next Obligation.
  apply QueMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply QueMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply QueMod.map_get_sig.
Qed.
Next Obligation.
  apply QueMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply QueMod.map_get_set.
Qed.
Next Obligation.
  apply QueMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply QueMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply QueMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply QueMod.map_set_emp.
Qed.
Next Obligation.
  apply QueMod.map_set_sig.
Qed.
Next Obligation.
  apply QueMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply QueMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply QueMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply QueMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply QueMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply QueMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply QueMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply QueMod.map_del_sem.
Qed.

Definition SourceDom := task_dom.
Definition DestDom := task_dom.

Definition size_t := nat. 

Inductive content_t := 
  SampleCh: val -> content_t 
| QueueCh: size_t -> vallist -> (* list tid ->  *)content_t
(* list of tasks waiting to receive from the channel *).  

Module chan.
  Definition B : Set := (SourceDom * DestDom * content_t)%type.  
  Definition holder : B := (Int.mone, Int.mone, SampleCh (Vint32 Int.mone)). 
End chan.

Module ChanMod := MapLib.MapFun chidspec chan.  

Program Instance ChanMap: PermMap chid (SourceDom * DestDom * content_t) ChanMod.map := 
  {
    usePerm := ChanMod.usePerm;
    isRw := ChanMod.isRw;
    flip := ChanMod.flip;
    sameV := ChanMod.sameV;
    same := ChanMod.same;
    emp := ChanMod.emp;
    join := ChanMod.join;
    del := ChanMod.del;
    get := ChanMod.get;
    set := ChanMod.set;
    sig := ChanMod.sig;
    merge := ChanMod.merge;
    minus := ChanMod.minus;
    map_dec_a := ChanMod.map_dec_a
}.
Next Obligation.
  apply ChanMod.map_join_emp.
Qed.
Next Obligation.
  apply ChanMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply ChanMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply ChanMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply ChanMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply ChanMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply ChanMod.map_eql; auto.
Qed.
Next Obligation.
  apply ChanMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply ChanMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply ChanMod.map_get_sig.
Qed.
Next Obligation.
  apply ChanMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply ChanMod.map_get_set.
Qed.
Next Obligation.
  apply ChanMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply ChanMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply ChanMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply ChanMod.map_set_emp.
Qed.
Next Obligation.
  apply ChanMod.map_set_sig.
Qed.
Next Obligation.
  apply ChanMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply ChanMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply ChanMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply ChanMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply ChanMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply ChanMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply ChanMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply ChanMod.map_del_sem.
Qed.


(* variables about Domain *)

Definition  dscdidx := int32.
Definition  dscdlen := int32.
Definition  cdom := int32.
Definition  ldom := int32.
Definition  dtime := int32.

Definition DSlength := int32.
Definition DSdomain := int32.

(* Module about abstract KsDomSchedule block *)

Module absdomscd.
  Definition B : Set := DSlength * DSdomain. 
  Definition holder : B := (Int.zero, Int.zero).
End absdomscd.

Module DScdMod := MapLib.MapFun idxspec absdomscd.

Program Instance DScdMap: PermMap int32 absdomscd.B DScdMod.map :=
 {
    usePerm := DScdMod.usePerm;
    isRw := DScdMod.isRw;
    flip := DScdMod.flip;
    sameV := DScdMod.sameV;
    same := DScdMod.same;
    emp := DScdMod.emp;
    join := DScdMod.join;
    del := DScdMod.del;
    get := DScdMod.get;
    set := DScdMod.set;
    sig := DScdMod.sig;
    merge := DScdMod.merge;
    minus := DScdMod.minus;
    map_dec_a := DScdMod.map_dec_a
}.

Next Obligation.
  apply DScdMod.map_join_emp.
Qed.
Next Obligation.
  apply DScdMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply DScdMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply DScdMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply DScdMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply DScdMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply DScdMod.map_eql; auto.
Qed.
Next Obligation.
  apply DScdMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply DScdMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply DScdMod.map_get_sig.
Qed.
Next Obligation.
  apply DScdMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply DScdMod.map_get_set.
Qed.
Next Obligation.
  apply DScdMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply DScdMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply DScdMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply DScdMod.map_set_emp.
Qed.
Next Obligation.
  apply DScdMod.map_set_sig.
Qed.
Next Obligation.
  apply DScdMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply DScdMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply DScdMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply DScdMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply DScdMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply DScdMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply DScdMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply DScdMod.map_del_sem.
Qed.

(* mapping from core ID to ID of current task on core *) 

Module coreidspec.
  Definition A := nat.
  Definition beq := beq_nat.
  Definition blt := Nat.ltb. 
 
Lemma beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.
Proof.
  intros.
  symmetry in H; apply beq_nat_eq in H.
  auto.
Qed.    

Lemma beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
Proof. 
  intros.
  pose proof Nat.eqb_spec.  
  specialize (H0 a a').
  destruct H0; auto.
  subst. rewrite Nat.eqb_refl in H. false. 
Qed.  

Lemma eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.
Proof.
  intros.
  rewrite H. apply Nat.eqb_refl. 
Qed.

Lemma neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.
Proof.
  intros.
  apply Nat.eqb_neq in H.
  unfold beq. auto.
Qed.

Lemma blt_trans : 
  forall a a' a'' : A,
    blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
Proof.
  unfold blt; intros.
  apply Nat.ltb_lt in H.
  apply Nat.ltb_lt in H0.
  apply Nat.ltb_lt.
  eauto with arith.
Qed.

Lemma blt_irrefl :
  forall a : A,
    blt a a = false.
Proof.  
  unfold blt; intros.
  apply Nat.ltb_irrefl.
Qed.

Lemma blt_asym : 
  forall a b : A, 
    blt a b = true -> blt b a = false.
Proof.  
  unfold blt; intros.
  apply Nat.ltb_lt in H.
  rewrite Nat.ltb_ge.
  eauto with arith.
Qed.

Import Lia. 

Lemma blt_beq_dec :
  forall a b : A,
    {blt a b = true} + {beq a b = true} + {blt b a = true}.
Proof.
  unfold blt; unfold beq; intros.
  remember (blt a b) as bool1; destruct bool1.
  left; left; auto.
  remember (beq a b) as bool2; destruct bool2.
  left; right; auto.
  right. 
  symmetry in Heqbool1; apply NPeano.Nat.ltb_ge in Heqbool1.
  unfold beq in Heqbool2.
  symmetry in Heqbool2; apply beq_nat_false in Heqbool2.
  rewrite Nat.ltb_lt.
  lia.
Qed.  

End coreidspec.

Module abscoretask.
  Definition B := tid.
  Definition holder : B := (xH, Int.zero).  
End abscoretask.

Module CoreTaskMod := MapLib.MapFun coreidspec abscoretask.  

Program Instance CoreTidMap: PermMap coreid abscoretask.B CoreTaskMod.map := 
 {
    usePerm := CoreTaskMod.usePerm;
    isRw := CoreTaskMod.isRw;
    flip := CoreTaskMod.flip;
    sameV := CoreTaskMod.sameV;
    same := CoreTaskMod.same;
    emp := CoreTaskMod.emp;
    join := CoreTaskMod.join;
    del := CoreTaskMod.del;
    get := CoreTaskMod.get;
    set := CoreTaskMod.set;
    sig := CoreTaskMod.sig;
    merge := CoreTaskMod.merge;
    minus := CoreTaskMod.minus;
    map_dec_a := CoreTaskMod.map_dec_a
}.

Next Obligation.
  apply CoreTaskMod.map_join_emp.
Qed.
Next Obligation.
  apply CoreTaskMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CoreTaskMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CoreTaskMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CoreTaskMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_eql; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CoreTaskMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_get_sig.
Qed.
Next Obligation.
  apply CoreTaskMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_get_set.
Qed.
Next Obligation.
  apply CoreTaskMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CoreTaskMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CoreTaskMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_set_emp.
Qed.
Next Obligation.
  apply CoreTaskMod.map_set_sig.
Qed.
Next Obligation.
  apply CoreTaskMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CoreTaskMod.map_del_sem.
Qed.


Module freetids.
  Definition B := list tid.
  Definition holder : B := nil.   
End freetids. 

Module FreeTidsMod := MapLib.MapFun idxspec freetids.   

Program Instance FreeTidsMap: PermMap task_dom freetids.B FreeTidsMod.map :=  
 {
    usePerm := FreeTidsMod.usePerm;
    isRw := FreeTidsMod.isRw;
    flip := FreeTidsMod.flip;
    sameV := FreeTidsMod.sameV;
    same := FreeTidsMod.same;
    emp := FreeTidsMod.emp;
    join := FreeTidsMod.join;
    del := FreeTidsMod.del;
    get := FreeTidsMod.get;
    set := FreeTidsMod.set;
    sig := FreeTidsMod.sig;
    merge := FreeTidsMod.merge;
    minus := FreeTidsMod.minus;
    map_dec_a := FreeTidsMod.map_dec_a
}.

Next Obligation.
  apply FreeTidsMod.map_join_emp.
Qed.
Next Obligation.
  apply FreeTidsMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply FreeTidsMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply FreeTidsMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply FreeTidsMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_eql; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply FreeTidsMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_get_sig.
Qed.
Next Obligation.
  apply FreeTidsMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_get_set.
Qed.
Next Obligation.
  apply FreeTidsMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply FreeTidsMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply FreeTidsMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_set_emp.
Qed.
Next Obligation.
  apply FreeTidsMod.map_set_sig.
Qed.
Next Obligation.
  apply FreeTidsMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply FreeTidsMod.map_del_sem.
Qed.


Module freeqids.
  Definition B := list qid.
  Definition holder : B := nil.   
End freeqids.  

Module FreeQidsMod := MapLib.MapFun idxspec freeqids.   

Program Instance FreeQidsMap: PermMap task_dom freeqids.B FreeQidsMod.map :=   
 {
    usePerm := FreeQidsMod.usePerm;
    isRw := FreeQidsMod.isRw;
    flip := FreeQidsMod.flip;
    sameV := FreeQidsMod.sameV;
    same := FreeQidsMod.same;
    emp := FreeQidsMod.emp;
    join := FreeQidsMod.join;
    del := FreeQidsMod.del;
    get := FreeQidsMod.get;
    set := FreeQidsMod.set;
    sig := FreeQidsMod.sig;
    merge := FreeQidsMod.merge;
    minus := FreeQidsMod.minus;
    map_dec_a := FreeQidsMod.map_dec_a
}.

Next Obligation.
  apply FreeQidsMod.map_join_emp.
Qed.
Next Obligation.
  apply FreeQidsMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply FreeQidsMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply FreeQidsMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply FreeQidsMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_eql; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply FreeQidsMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_get_sig.
Qed.
Next Obligation.
  apply FreeQidsMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_get_set.
Qed.
Next Obligation.
  apply FreeQidsMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply FreeQidsMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply FreeQidsMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_set_emp.
Qed.
Next Obligation.
  apply FreeQidsMod.map_set_sig.
Qed.
Next Obligation.
  apply FreeQidsMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply FreeQidsMod.map_del_sem.
Qed.


Module intquant.
  Definition B : Set := int32%type.  
  Definition holder : B := Int.zero. 
End intquant.

Module CoreIntMod := MapLib.MapFun coreidspec intquant.  

Program Instance CoreIntMap: PermMap coreid intquant.B CoreIntMod.map := 
  {
    usePerm := CoreIntMod.usePerm;
    isRw := CoreIntMod.isRw;
    flip := CoreIntMod.flip;
    sameV := CoreIntMod.sameV;
    same := CoreIntMod.same;
    emp := CoreIntMod.emp;
    join := CoreIntMod.join;
    del := CoreIntMod.del;
    get := CoreIntMod.get;
    set := CoreIntMod.set;
    sig := CoreIntMod.sig;
    merge := CoreIntMod.merge;
    minus := CoreIntMod.minus;
    map_dec_a := CoreIntMod.map_dec_a
}.
Next Obligation.
  apply CoreIntMod.map_join_emp.
Qed.
Next Obligation.
  apply CoreIntMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CoreIntMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CoreIntMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CoreIntMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CoreIntMod.map_eql; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CoreIntMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CoreIntMod.map_get_sig.
Qed.
Next Obligation.
  apply CoreIntMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_get_set.
Qed.
Next Obligation.
  apply CoreIntMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CoreIntMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CoreIntMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CoreIntMod.map_set_emp.
Qed.
Next Obligation.
  apply CoreIntMod.map_set_sig.
Qed.
Next Obligation.
  apply CoreIntMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CoreIntMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CoreIntMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CoreIntMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CoreIntMod.map_del_sem.
Qed.


Module dscdmap.
  Definition B := DScdMod.map.  
  Definition holder : B := emp: DScdMod.map . 
End dscdmap.

Module CoreDScdMod := MapLib.MapFun coreidspec dscdmap.  

Program Instance CoreDScdMap: PermMap coreid dscdmap.B CoreDScdMod.map := 
  {
    usePerm := CoreDScdMod.usePerm;
    isRw := CoreDScdMod.isRw;
    flip := CoreDScdMod.flip;
    sameV := CoreDScdMod.sameV;
    same := CoreDScdMod.same;
    emp := CoreDScdMod.emp;
    join := CoreDScdMod.join;
    del := CoreDScdMod.del;
    get := CoreDScdMod.get;
    set := CoreDScdMod.set;
    sig := CoreDScdMod.sig;
    merge := CoreDScdMod.merge;
    minus := CoreDScdMod.minus;
    map_dec_a := CoreDScdMod.map_dec_a
}.
Next Obligation.
  apply CoreDScdMod.map_join_emp.
Qed.
Next Obligation.
  apply CoreDScdMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CoreDScdMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CoreDScdMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CoreDScdMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_eql; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CoreDScdMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_get_sig.
Qed.
Next Obligation.
  apply CoreDScdMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_get_set.
Qed.
Next Obligation.
  apply CoreDScdMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CoreDScdMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CoreDScdMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_set_emp.
Qed.
Next Obligation.
  apply CoreDScdMod.map_set_sig.
Qed.
Next Obligation.
  apply CoreDScdMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CoreDScdMod.map_del_sem.
Qed.


(* Definition bufmp := task_dom -> list msg. *)


Inductive absdata := 
| abstcblist: TcbMod.map -> absdata
| absecblist: QueMod.map -> absdata
| chanlist: ChanMod.map -> absdata
| freetidlist: FreeTidsMod.map -> absdata 
| freeqidlist: FreeQidsMod.map -> absdata 
| ostm: ostime -> absdata
| oscoret: CoreTaskMod.map -> absdata                    
(* | oscurt: addrval -> absdata *)
(* | tskctrlst: TskCtrlStMod.map -> absdata  *)
| dschedidx: CoreIntMod.map (* dscdidx *) -> absdata 
| dschedlen: CoreIntMod.map (* dscdlen *) -> absdata 
| curdom: CoreIntMod.map (* cdom *) -> absdata 
| lastdom: CoreIntMod.map (* ldom *) -> absdata 
| domtime: CoreIntMod.map (* dtime *) -> absdata  
| dsched: CoreDScdMod.map (* DScdMod.map *) -> absdata (* the partition scheduling table *)

(* | ibufs: bufmp -> absdata *)
(* | obufs: bufmp -> absdata *)
.

Module absdatastru.
 
 Definition B := absdata. 
 Definition holder : B := (abstcblist emp).
 
End absdatastru.

Module OSAbstMod := MapLib.MapFun absdataidspec absdatastru.

Definition osabst:= OSAbstMod.map. 

Program Instance AMap: PermMap absdataid absdata osabst :=
  {
    usePerm := OSAbstMod.usePerm;
    isRw := OSAbstMod.isRw;
    flip := OSAbstMod.flip;
    sameV := OSAbstMod.sameV;
    same := OSAbstMod.same;
    emp := OSAbstMod.emp;
    join := OSAbstMod.join;
    del := OSAbstMod.del;
    get := OSAbstMod.get;
    set := OSAbstMod.set;
    sig := OSAbstMod.sig;
    merge := OSAbstMod.merge;
    minus := OSAbstMod.minus;
    map_dec_a := OSAbstMod.map_dec_a
  }.
Next Obligation.
  apply OSAbstMod.map_join_emp.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_eql; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_sig.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_set.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_set_emp.
Qed.
Next Obligation.
  apply OSAbstMod.map_set_sig.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_del_sem.
Qed.


(************************ Defining the invariant ************************)  


Definition ex_active_tsk (O: osabst) (t: tid) (td: task_dom) :=
  exists tls pr st msg (* cm  *)sus, 
    get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (pr, st, msg, (* cm,  *)sus, td).

Definition ex_free_tsk (O: osabst) (t: tid) (td: task_dom) :=
  exists fts ts,
    get O freetid = Some (freetidlist fts) /\
      get fts td = Some ts /\
      List.In t ts. 

Definition sdom_ (O: osabst) (t: tid) (td: task_dom) : Prop :=
  ex_active_tsk O t td \/ ex_free_tsk O t td.

(* Definition dom_of_tsk_ext (t: tid) (O: osabst) (td: task_dom) := *)
(*   (exists tls pr st msg sus, *)
(*       get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (pr, st, msg, sus, td)) *)
(*   \/ *)
(*     (exists fts ts, get O freetid = Some (freetidlist fts) /\ get fts td = Some ts /\ In t ts). *)


Definition ex_active_que (O: osabst) (q: qid) (td: task_dom) :=
  exists qls ms sz ts, 
    get O quelsid = Some (absecblist qls) /\
      get qls q = Some (msgq ms sz ts, td).

Definition ex_free_que (O: osabst) (q: qid) (td: task_dom) :=
  exists fqs qs,
    get O freeqid = Some (freeqidlist fqs) /\
      get fqs td = Some qs /\
      List.In q qs.

Definition q_sdom_ (O: osabst) (q: qid) (td: task_dom) : Prop :=
  ex_active_que O q td \/ ex_free_que O q td.

(* Definition dom_of_mq_ext (q: qid) (O: osabst)(td: task_dom) := *)
(*   ( *)
(*     (exists qls ms sz ts, *)
(*         get O quelsid = Some (absecblist qls) /\ get qls q = Some (msgq ms sz ts, td)) *)
(*     \/ *)
(*       (exists fqs qs, get O freeqid = Some (freeqidlist fqs) /\ get fqs td = Some qs /\ In q qs) *)
(*   ). *)


Definition tsk_active_free_disj (O: osabst) :=
  forall t td, 
    ex_active_tsk O t td -> ex_free_tsk O t td -> False. 
      (*  /\ *)
      (* (ex_free_tsk O t td -> ~ex_active_tsk O t td).  *)

Definition tsk_dom_disj (O: osabst) :=
  forall t td1 td2,
    sdom_ O t td1 -> sdom_ O t td2 -> td1 = td2.

Definition que_active_free_disj (O: osabst) :=
  forall q td,
    ex_active_que O q td -> ex_free_que O q td -> False. 
      (*  /\ *)
      (* (ex_free_que O q td -> ~ex_active_que O q td).  *)

Definition que_dom_disj (O: osabst) :=
  forall q td1 td2, 
    q_sdom_ O q td1 -> q_sdom_ O q td2 -> td1 = td2.

Definition tsk_diff_id_prio (O: osabst) :=
  forall tls, 
    get O abstcblsid = Some (abstcblist tls) ->
    forall t1 t2 td pr1 st1 msg1 (* cm1  *)sus1 pr2 st2 msg2 (* cm2  *)sus2, 
      t1 <> t2 ->
      get tls t1 = Some (pr1, st1, msg1, (* cm1,  *)sus1, td) ->
      get tls t2 = Some (pr2, st2, msg2, (* cm2,  *)sus2, td) -> 
      pr1 <> pr2. 

Definition mq_wt_cond (O: osabst) :=
  forall qls q ms sz ts td tls t, 
    get O quelsid = Some (absecblist qls) ->
    get O abstcblsid = Some (abstcblist tls) ->
    get qls q = Some (msgq ms sz ts, td) ->
    List.In t ts ->
    exists pr msg (* cm *) sus to,
      get tls t = Some (pr, wait (os_stat_qpend q) to, msg, (* cm,  *)sus, td). 

Definition wt_mq_cond (O: osabst) :=
  forall qls tls t pr q to msg sus td, 
    get O abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (pr, wait (os_stat_qpend q) to, msg, sus, td) ->
    get O quelsid = Some (absecblist qls) ->
    exists ms sz ts, 
      get qls q = Some (msgq ms sz ts, td) /\ List.In t ts. 

Inductive chtype := Sampling | Queuing. 

Module chcfg_t.
  Definition B : Set := (SourceDom * DestDom * chtype)%type.   
  Definition holder : B := (Int.mone, Int.mone, Sampling).  
End chcfg_t.

Module ChsCfgMod := MapLib.MapFun chidspec chcfg_t.  

Program Instance ChsCfgMap: PermMap chid chcfg_t.B ChsCfgMod.map := 
  {
    usePerm := ChsCfgMod.usePerm;
    isRw := ChsCfgMod.isRw;
    flip := ChsCfgMod.flip;
    sameV := ChsCfgMod.sameV;
    same := ChsCfgMod.same;
    emp := ChsCfgMod.emp;
    join := ChsCfgMod.join;
    del := ChsCfgMod.del;
    get := ChsCfgMod.get;
    set := ChsCfgMod.set;
    sig := ChsCfgMod.sig;
    merge := ChsCfgMod.merge;
    minus := ChsCfgMod.minus;
    map_dec_a := ChsCfgMod.map_dec_a
}.
Next Obligation.
  apply ChsCfgMod.map_join_emp.
Qed.
Next Obligation.
  apply ChsCfgMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply ChsCfgMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply ChsCfgMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply ChsCfgMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_eql; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply ChsCfgMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_get_sig.
Qed.
Next Obligation.
  apply ChsCfgMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_get_set.
Qed.
Next Obligation.
  apply ChsCfgMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply ChsCfgMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply ChsCfgMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_set_emp.
Qed.
Next Obligation.
  apply ChsCfgMod.map_set_sig.
Qed.
Next Obligation.
  apply ChsCfgMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply ChsCfgMod.map_del_sem.
Qed.

(* the configuration about channels *)
Parameter chcfg : ChsCfgMod.map.

Definition chs_sat_config (O: osabst) :=
  forall chs c sd dd content, 
    get O chlsid = Some (chanlist chs) ->
    get chs c = Some (sd, dd, content) ->
    (((exists v, content = SampleCh v) /\ get chcfg c = Some (sd, dd, Sampling)) \/
       (exists sz vl, content = QueueCh sz vl) /\ get chcfg c = Some (sd, dd, Queuing)). 
      

(* Record dsch_data_valid (O: osabst) := *)
(*   { *)
(*     dv_len_rgn: *)
(*     forall lenmp len cid, *)
(*       get O dschedlenid = Some (dschedlen lenmp) ->  *)
(*       get lenmp cid = Some len -> *)
(*       (Int.ltu Int.zero len = true /\ Int.ltu len (Int.repr 64%Z) = true); *)

(*     dv_idx_rgn: *)
(*     forall lenmp len idxmp idx cid,  *)
(*       get O dschedlenid = Some (dschedlen lenmp) ->  *)
(*       get lenmp cid = Some len -> *)
(*       get O dschedidxid = Some (dschedidx idxmp) -> *)
(*       get idxmp cid = Some idx -> *)
(*       (Int.ltu Int.zero idx = true /\ Int.ltu idx len = true);  *)

(*     dv_tbl_valid:  *)
(*     forall lenmp len schmp schtbl cid, *)
(*       get O dschedlenid = Some (dschedlen lenmp) ->  *)
(*       get lenmp cid = Some len -> *)
(*       get O dschedid = Some (dsched schmp) -> *)
(*       get schmp cid = Some schtbl ->  *)
(*       (forall j, *)
(*           ((Int.eq j Int.zero || Int.ltu Int.zero j) && Int.ltu j len) = true ->  *)
(*           exists t d, get schtbl j = Some (t, d))  *)
(*   }.  *)


Record I_ (O: osabst) : Prop := { 
    inv_tsk_af_disj: tsk_active_free_disj O;
    inv_tsk_d_disj: tsk_dom_disj O;
    inv_tsk_diff_idpr: tsk_diff_id_prio O; 
    inv_que_af_disj: que_active_free_disj O;
    inv_que_d_disj: que_dom_disj O; 
    inv_mq_wt: mq_wt_cond O;
    inv_wt_mq: wt_mq_cond O; 
    (* inv_wtc: wt_chan_cond O; *)
    inv_chcfg: chs_sat_config O(* ;  *)
    (* inv_dschd_valid: dsch_data_valid O *) 
  }.


(************************ Instantating the type class State ************************) 

Definition get_cur_tsk (O: osabst) (cid: coreid) (t: tid) : Prop := 
  exists ct,
    get O coretid = Some (oscoret ct) /\
      get ct cid = Some t.

Definition get_cur_dom (O: osabst) (cid: coreid) (td: task_dom) : Prop := 
  exists cdmp, 
    get O curdomid = Some (curdom cdmp) /\
      get cdmp cid = Some td.

Definition upd_cur_tsk_ (O: osabst) (cid: coreid) (t: tid) (O': osabst) :=
  exists ct ct',
    get O coretid = Some (oscoret ct) /\
      ct' = set ct cid t /\ 
      O' = set O coretid (oscoret ct'). 
    
Definition upd_cur_dom_ (O: osabst) (cid: coreid) (td: task_dom) (O': osabst) :=
  exists cdmp cdmp',
    get O curdomid = Some (curdom cdmp) /\
      cdmp' = set cdmp cid td /\
      O' = set O curdomid (curdom cdmp'). 

Ltac is_fn_prover :=
  match goal with
    H: _ _ _, H': _ _ _ |- _ => unfolds in H; unfolds in H'; simpljoin; congruence
  end.

(* Definition inv (O: osabst) := True. *)

(* Definition core_of_dom_ (O: osabst) (td: task_dom) (cid: coreid) := *)
(*   exists schmp schtbl idx len,  *)
(*     get O dschedid = Some (dsched schmp) /\ *)
(*       get schmp cid = Some schtbl /\ *)
(*       get schtbl idx = Some (len, td).   *)

Program Instance state : State osabst := {
    (* state_t := osabst;  *)
    I := I_;  
    sdom := sdom_;
    cur_tsk := get_cur_tsk;
    cur_dom := get_cur_dom;
    (* core_of_dom := core_of_dom_;  *)
    upd_cur_tsk := upd_cur_tsk_;
    upd_cur_dom := upd_cur_dom_
}.
Next Obligation.
is_fn_prover. 
Qed. 

Next Obligation.
is_fn_prover.
Qed.

Next Obligation.
  is_fn_prover.
Qed. 

Next Obligation.
  is_fn_prover.
Qed.

  (* unfold sdom_ in *.  *)
  (* destruct H0; destruct H1. *)
  (* - *)
  (*   unfold ex_active_tsk in *. *)
  (*   simpljoin. *)
  (*   rewrite H0 in H1. inverts H1. *)
  (*   rewrite H2 in H3. inverts H3. *)
  (*   auto. *)
  (* - *)
  (*   assert (Hsd1: sdom_ O t td1). *)
  (*   { unfolds; eauto. } *)
  (*   assert (Hsd2: sdom_ O t td2). *)
  (*   { unfolds; eauto. } *)
  (*   inverts H. *)
  (*   eapply inv_tsk_d_disj0 in Hsd1. *)
  (*   casetac td1 td2 He Hne. *)
  (*   + auto. *)
  (*   + eapply Hsd1 in Hsd2; eauto. false.  *)
  (* - *)

Next Obligation. (* sdom is partial func *)
  inverts H.
  eapply inv_tsk_d_disj0; eauto.
Qed.

Next Obligation. (* upd_cur_tsk_eq *)
  inverts H.
  simpljoin.
  unfolds.
  rewrite map_get_set.
  eexists.
  splits; eauto.
  rewrite map_get_set.
  auto.
Qed.

Next Obligation. (* upd_cur_tsk_neq *)
  inverts H0.
  simpljoin.
  unfolds.
  unfold get_cur_tsk.
  rewrite map_get_set.
  split.
  -
    introv Hct.
    simpljoin.
    eexists; splits; eauto.
    rewrite neq_set_get; eauto.
    congruence.
  -
    introv Hct.
    simpljoin.
    eexists; splits; eauto.
    inverts H1.
    rewrite neq_set_get in H2; eauto.    
Qed.

Next Obligation. (* upd_cur_dom_eq *) 
  inverts H.
  simpljoin.
  unfolds.
  rewrite map_get_set.
  eexists.
  splits; eauto.
  rewrite map_get_set.
  auto.
Qed. 

Next Obligation. (* upd_cur_dom_neq *)
  inverts H0.
  simpljoin.
  unfolds.
  unfold get_cur_dom.
  rewrite map_get_set.
  split.
  -
    introv Hct.
    simpljoin.
    eexists; splits; eauto.
    rewrite neq_set_get; eauto.
    congruence.
  -
    introv Hct.
    simpljoin.
    eexists; splits; eauto.
    inverts H1.
    rewrite neq_set_get in H2; eauto.    
Qed. 

Next Obligation.
  unfolds in H.
  destruct H as (ct & ct' & Hgct & Hct' & HO').
  subst.
  unfolds.
  unfolds get_cur_dom.
  rewrite neq_set_get; eauto.
  introv Hf. inverts Hf.
Qed. 

