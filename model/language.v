
Require Export Integers.
Require Import memory.

(* Require Export Coq.Classes.RelationClasses.  *)

Definition coreid := nat.
Definition task_dom := int. 

Set Universe Polymorphism.

Class State (state_t: Type) := 
  {
    (* state_t: Type; *)
    I : state_t -> Prop; 

    sdom: state_t -> tid -> task_dom -> Prop;
    cur_tsk: state_t -> coreid -> tid -> Prop;
    cur_dom: state_t -> coreid -> task_dom -> Prop; 
    (* core_of_dom: state_t -> task_dom -> coreid -> Prop;  *)
    upd_cur_tsk: state_t -> coreid -> tid -> state_t -> Prop;
    upd_cur_dom: state_t -> coreid -> task_dom -> state_t -> Prop; 

    cur_tsk_is_fn:
    forall O cid t1 t2, I O -> cur_tsk O cid t1 -> cur_tsk O cid t2 -> t1 = t2; 
    cur_dom_is_fn:
    forall O cid td1 td2, I O -> cur_dom O cid td1 -> cur_dom O cid td2 -> td1 = td2; 
    (* core_of_dom_is_fn: *)
    (* forall O td cid1 cid2, I O -> core_of_dom O td cid1 -> core_of_dom O td cid2 -> cid1 = cid2;  *)
    upd_cur_tsk_is_fn:
    forall O cid t O1 O2, I O -> upd_cur_tsk O cid t O1 -> upd_cur_tsk O cid t O2 -> O1 = O2;
    upd_cur_dom_is_fn:
    forall O cid td O1 O2, I O -> upd_cur_dom O cid td O1 -> upd_cur_dom O cid td O2 -> O1 = O2; 
    sdom_is_fn:
    forall O t td1 td2, I O -> sdom O t td1 -> sdom O t td2 -> td1 = td2;
    
    upd_cur_tsk_eq:
    forall O O' cid t, upd_cur_tsk O cid t O' -> cur_tsk O' cid t; 
    upd_cur_tsk_neq:
    forall O O' cid cid' t',
      cid <> cid' ->       
      upd_cur_tsk O cid' t' O' -> 
      (forall t, cur_tsk O cid t <-> cur_tsk O' cid t);  
    
    upd_cur_dom_eq: 
    forall O O' cid td, upd_cur_dom O cid td O' -> cur_dom O' cid td; 
    upd_cur_dom_neq:
    forall O O' cid cid' td',
      cid <> cid' -> 
      upd_cur_dom O cid' td' O' -> 
      (forall td, cur_dom O cid td <-> cur_dom O' cid td);

    upd_cur_tsk_prsv_cur_dom:
    forall O cid t O', 
      upd_cur_tsk O cid t O' ->
      (forall cid td, cur_dom O cid td <-> cur_dom O' cid td) 
  }.

Unset Universe Polymorphism.

Definition fid :=  ident.

Inductive sem_act :=
  _TauAct | _CallAct (f: fid) (vl: vallist) | 
  _TCreAct (t: tid) (fp: ufid) (argp: addrval) | _TDelAct (t: tid) |
  _TickAct (cid: coreid).  

Definition osabstep `{State} := tid -> vallist -> state_t -> sem_act -> (vallist * state_t) -> Prop.
(* Definition osabstep := tid -> vallist -> osabst -> sem_act -> (vallist * osabst) -> Prop.  *)

Definition preasrt_t `{State} := tid -> state_t -> Prop.
Definition trivial_asrt `{State} : preasrt_t := fun _ _ => True.

Definition bool_expr := vallist -> bool.

Inductive spec_code `{State} :=
| spec_prim :  preasrt_t -> vallist-> osabstep -> spec_code
| sched : preasrt_t -> spec_code
| spec_done : vallist -> spec_code
| spec_seq : spec_code -> (vallist -> spec_code) -> spec_code
| spec_dowh: spec_code -> bool_expr -> spec_code
. 

Definition spec_skip_step `{State}
  (t: tid) (vl: vallist) (O: state_t) (act: sem_act) (res: vallist * state_t) :=
  let (vl', O') := res in (vl' = nil /\ O' = O /\ act = _TauAct).

Definition spec_skip `{State} : spec_code := spec_prim trivial_asrt nil spec_skip_step.

Notation " x '(|' vl '|)' " := (spec_prim trivial_asrt vl x) (at level 40).
Notation  " 'END' v " := (spec_done v) (at level 40).
Notation  " x ';;' y " := (spec_seq x (fun _ => y)) (right associativity, at level 44). 
Notation " x ';;>' y" := (spec_seq x y) (right associativity, at level 44). 

Notation "asrt '#' x '[|' vl '|]' " := (spec_prim asrt vl x) (at level 40). 

Set Implicit Arguments.
Unset Strict Implicit.

Parameter strat_state_t: Type.
Parameter def_strat_state: strat_state_t.

Definition strat_t := strat_state_t -> val -> (sem_act * strat_state_t).  

Definition def_strat: strat_t := (fun _ => fun _ => (_TauAct, def_strat_state)). 

Open Scope type_scope.

Inductive cureval `{State} :=
| cur_stmt : spec_code -> cureval
| cur_strat : strat_t -> cureval. 

Definition hid := nat.

Inductive cont `{State} :=  
| kstop : cont
| kenknl : fid -> strat_t -> cont -> cont
| kevent : hid -> cureval -> cont -> cont. 
(* level-i interrupt while executing spec code *) 

Definition code `{State} := (cureval * cont). 

Definition tasks `{State} := tid -> option code.

Module ustratstate.
  Definition B := strat_state_t.  
  Definition holder : B := def_strat_state.  
End ustratstate. 

Module StratStateMod := MapLib.MapFun idxspec ustratstate. 
(* one strategy state for each domain *) 

Definition ustate := StratStateMod.map.

(* instantiation *) 
Program Instance UStateMap: PermMap int ustratstate.B ustate :=
  {
    usePerm := StratStateMod.usePerm;
    isRw := StratStateMod.isRw;
    flip := StratStateMod.flip;
    sameV := StratStateMod.sameV;
    same := StratStateMod.same;
    emp := StratStateMod.emp;
    join := StratStateMod.join;
    del := StratStateMod.del;
    get := StratStateMod.get;
    set := StratStateMod.set;
    sig := StratStateMod.sig;
    merge := StratStateMod.merge;
    minus := StratStateMod.minus;
    map_dec_a := StratStateMod.map_dec_a
  }.
Next Obligation.
  apply StratStateMod.map_join_emp.
Qed.
Next Obligation.
  apply StratStateMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply StratStateMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply StratStateMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply StratStateMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply StratStateMod.map_eql; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply StratStateMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply StratStateMod.map_get_sig.
Qed.
Next Obligation.
  apply StratStateMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_get_set.
Qed.
Next Obligation.
  apply StratStateMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply StratStateMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply StratStateMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply StratStateMod.map_set_emp.
Qed.
Next Obligation.
  apply StratStateMod.map_set_sig.
Qed.
Next Obligation.
  apply StratStateMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply StratStateMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply StratStateMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply StratStateMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply StratStateMod.map_del_sem.
Qed.


Definition funtype : Set := prod type typelist.
Definition api_code `{State} := vallist -> spec_code.

Definition osapi `{State} := prod api_code  funtype.
Definition osapispec `{State} :=  fid -> option osapi.

Definition int_code `{State} := spec_code.
Definition osintspec `{State} := hid -> option int_code.

Definition ossched `{State} := state_t -> task_dom -> tid -> Prop. 

Definition osspec `{State} := (osapispec * osintspec * ossched). 

Definition world `{State} := (tasks * ustate * state_t).   


Module ufunc.
  Definition B := val -> strat_t.
  Definition holder : B := (fun _ => def_strat). 
End ufunc.

Module UfuncMod := MapLib.MapFun ufidspec ufunc.   

Program Instance UfuncMap: PermMap ufid ufunc.B UfuncMod.map :=  
  {
    usePerm := UfuncMod.usePerm;
    isRw := UfuncMod.isRw;
    flip := UfuncMod.flip;
    sameV := UfuncMod.sameV;
    same := UfuncMod.same;
    emp := UfuncMod.emp;
    join := UfuncMod.join;
    del := UfuncMod.del;
    get := UfuncMod.get;
    set := UfuncMod.set;
    sig := UfuncMod.sig;
    merge := UfuncMod.merge;
    minus := UfuncMod.minus;
    map_dec_a := UfuncMod.map_dec_a
}.
Next Obligation.
  apply UfuncMod.map_join_emp.
Qed.
Next Obligation.
  apply UfuncMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply UfuncMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply UfuncMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply UfuncMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply UfuncMod.map_eql; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply UfuncMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply UfuncMod.map_get_sig.
Qed.
Next Obligation.
  apply UfuncMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_get_set.
Qed.
Next Obligation.
  apply UfuncMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply UfuncMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply UfuncMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply UfuncMod.map_set_emp.
Qed.
Next Obligation.
  apply UfuncMod.map_set_sig.
Qed.
Next Obligation.
  apply UfuncMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply UfuncMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply UfuncMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply UfuncMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply UfuncMod.map_del_sem.
Qed.

Definition uprogs_t := UfuncMod.map. 

