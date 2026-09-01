
Require Import memory.
Require Import language.
Require Import opsem. 

Require Import Coq.Classes.RelationClasses.

Section DeductRules.

Context {state_t : Type}.  
Context `{State state_t}. 
    
Definition rg_t := state_t -> state_t -> Prop.

Definition preasrt_t := tid -> state_t -> Prop. 
Definition postasrt_t := tid -> vallist -> state_t -> Prop.  

Definition pre1 t O (p: preasrt_t) := p t O /\ I O.

Definition post1 t O vl' O' (q: postasrt_t) (guar: rg_t) := 
  q t vl' O' /\ I O' /\ guar O O'.
(* get O curdomid = get O' curdomid.  *) (* not sat for a tick *) 

Fixpoint head_sat (t: tid) O (s: spec_code) : Prop :=
  match s with
    spec_prim p vl step => p t O
  | sched p => p t O 
  | spec_done vl => True
  | spec_seq s0 vs => head_sat t O s0
  (* | spec_case p ss => p t O *)
  | spec_dowh s b => head_sat t O s
  end.

(* (t, Sigma) |= (s, q) *) 
Definition sat_stmt_post t (O: state_t) (s: spec_code) (q: postasrt_t) := 
  match s with
    spec_done vl => q t vl O
  | _ => head_sat t O s
  end.
    
Definition swi_changes (O O': state_t) : Prop :=
  exists cid t, upd_cur_tsk O cid t O'. 
  (* exists ct', O' = set O coretid (oscoret ct').  *)

Definition stable_pre (t: tid) (p: preasrt_t) (rly: rg_t) := 
  forall O O',
    p t O ->
    (rly O O' \/ swi_changes O O') ->
    p t O'. 

Definition dt_obeq_t := dom -> state_t -> state_t -> Prop.

Definition flows_to_t := dom -> dom -> Prop.

Definition pre2 
  t (O1 O2: state_t) (p: preasrt_t) (td: task_dom) (dobeq: dt_obeq_t) (flt: flows_to_t) := 
  
  pre1 t O1 p /\ pre1 t O2 p /\
    (* dobeq (SchedDom) O1 O2 /\  *)
    dobeq (TaskDom td) O1 O2 /\
    (* sdom t O1 = sdom t O2 /\  *)
    exists td',
      sdom O1 t td' /\ sdom O2 t td' /\ flt (TaskDom td') (TaskDom td) /\ dobeq (TaskDom td') O1 O2. 

Inductive deduct_rules : 
  tid -> rg_t -> rg_t -> flows_to_t -> dt_obeq_t -> spec_code -> postasrt_t -> Prop := 

  prim_rule:
    forall p q (step: osabstep) vl rly guar (dobeq: dt_obeq_t) (flt: flows_to_t) t,
      stable_pre t p rly ->
      (* stable_post t q rly -> *)
      (forall O O' vl' ac,
          pre1 t O p -> 
          step t vl O ac (vl', O') ->
          (post1 t O vl' O' q guar /\
             (forall t td, sdom O t td <-> sdom O' t td) /\  
             (forall t' a1 a2, ac = _TCreAct t' a1 a2 -> (t <> t' /\ (forall td, sdom O t td <-> sdom O t' td))) /\ 
             ((~exists cid, ac = _TickAct cid) ->
                (forall td d, sdom O t td -> ~(flt (TaskDom td) d) -> dobeq d O O')))
      ) ->
      (
        forall (O1 O2 O1' O2': state_t) (vl1' vl2': vallist) ac1 ac2 (td: task_dom),
          pre2 t O1 O2 p td dobeq flt ->
          step t vl O1 ac1 (vl1', O1') ->
          step t vl O2 ac2 (vl2', O2') ->
          (~exists cid, ac1 = _TickAct cid) ->
          (~exists cid, ac2 = _TickAct cid) -> 
          (dobeq (TaskDom td) O1' O2' /\ ac1 = ac2 /\ vl1' = vl2') 
      ) -> 
      deduct_rules t rly guar flt dobeq (spec_prim p vl step) q

| seq_rule:
  forall t rly guar dobeq flt s1 (vs2: vallist -> spec_code) q' q,
    deduct_rules t rly guar flt dobeq s1 q' ->
    (forall vl O s2,
        I O -> q' t vl O -> vs2 vl = s2 ->
        (sat_stmt_post t O s2 q /\ deduct_rules t rly guar flt dobeq s2 q)) ->
    deduct_rules t rly guar flt dobeq (spec_seq s1 vs2) q

| dowh_rule:
  forall t rly guar dobeq flt s (b: bool_expr) (q' q: postasrt_t), 
    deduct_rules t rly guar flt dobeq s q' ->
    (forall O vl, I O -> q' t vl O -> b vl = true -> head_sat t O s) ->
    (forall O vl, I O -> q' t vl O -> b vl = false -> q t vl O) -> 
    (* stable_post t q rly -> *)
    deduct_rules t rly guar flt dobeq (spec_dowh s b) q

| sched_rule:
  forall t rly guar dobeq flt p (q: postasrt_t),
    stable_pre t p rly ->
    (* stable_post t q rly ->  *)
    (forall O, pre1 t O p -> q t nil O) ->
    deduct_rules t rly guar flt dobeq (sched p) q
  
| end_rule:
  forall t rly guar dobeq flt vl q,
    (* stable_post t q rly ->  *)
    deduct_rules t rly guar flt dobeq (spec_done vl) q.  
  

Definition rg_env_t := tid -> rg_t. 

Definition well_rg (rly_tsk guar_tsk rly_itp guar_itp: rg_env_t) : Prop := 
  (forall t O, guar_tsk t O O /\ guar_itp t O O) /\ 
    (forall t t' O O',
        (guar_itp t O O' -> (rly_tsk t' O O' /\ rly_itp t' O O')) /\
          (t <> t' -> guar_tsk t O O' -> (rly_tsk t' O O' /\ rly_itp t' O O'))). 


Definition tsk_same_dom (dteq: dt_obeq_t) :=
  forall td O1 O2 t,
    I O1 -> I O2 -> dteq (TaskDom td) O1 O2 ->
    (sdom O1 t td <-> sdom O2 t td).

Definition sched_inv (sd: ossched) :=  
  forall O cid td t' O',
    I O ->
    cur_dom O cid td -> 
    sd O td t' ->
    upd_cur_tsk O cid t' O' -> 
    I O'.

Definition sched_same_dom (sd: ossched) := 
  forall O O' cid td t',
    I O ->
    cur_dom O cid td ->
    sd O td t' ->
    upd_cur_tsk O cid t' O' -> 
    (forall t td, sdom O t td <-> sdom O' t td). 

Fixpoint has_tick' (s: spec_code) t cid O vl' O' := 
  match s with
    spec_prim p vl step =>
      step t vl O (_TickAct cid) (vl', O')
  | spec_seq s1 vs2 =>
      has_tick' s1 t cid O vl' O' \/ exists vl_, has_tick' (vs2 vl_) t cid O vl' O'
  | spec_done vl =>
      False
  | spec_dowh s b => 
      has_tick' s t cid O vl' O' 
  | sched p => False
  end.

Definition has_tick (ispc: osintspec) t cid O vl' O' :=
  exists i s, ispc i = Some s /\ has_tick' s t cid O vl' O'.

Definition tick_dt_equiv (ispc: osintspec) (dteq: dt_obeq_t) := 
  forall O1 O2 O1' O2' t1 t2 vl1' vl2' cid d,
    I O1 -> I O2 ->
    dteq SchedDom O1 O2 ->
    dteq d O1 O2 ->
    has_tick ispc t1 cid O1 vl1' O1' ->
    has_tick ispc t2 cid O2 vl2' O2' ->
    (* (forall td, d = TaskDom td -> sdom t1 O1 td -> t1 = t2) ->  *) 
    (dteq d O1' O2' /\ vl1' = vl2').

Definition tick_cdom_eq (ispc: osintspec) (dteq: dt_obeq_t) := 
  forall O1 O2 O1' O2' t1 t2 vl1' vl2' cid,
    I O1 -> I O2 ->
    dteq SchedDom O1 O2 ->
    has_tick ispc t1 cid O1 vl1' O1' ->
    has_tick ispc t2 cid O2 vl2' O2' ->
    (forall td, cur_dom O1' cid td <-> cur_dom O2' cid td). 

Definition tick_preserves_cdom (ispc: osintspec) (dteq: dt_obeq_t) := 
  forall t cid cid' vl O O', 
    I O ->
    has_tick ispc t cid O vl O' ->
    cid <> cid' -> 
    (forall td, cur_dom O cid' td <-> cur_dom O' cid' td).   

Definition no_tick_in_kfunc (aspc: osapispec) :=
  forall f vl acode ftp,
    aspc f = Some (acode, ftp) ->
    forall t cid O vl' O', ~has_tick' (acode vl) t cid O vl' O'. 

(* Definition tick_output_eq (ispc: osintspec) := *)
(*   exists vl0, (forall t cid O vl' O', I O -> has_tick ispc t cid O vl' O' -> vl' = vl0).  *)
  
Definition swi_dteq (dteq: dt_obeq_t) := 
  forall O O' cid t d, upd_cur_tsk O cid t O' -> dteq d O O'. 

Definition sched_same_choice (sd: ossched) (dteq: dt_obeq_t) := 
  forall O1 O2 td, 
    I O1 -> I O2 ->
    dteq (TaskDom td) O1 O2 ->
    (forall t, sd O1 td t <-> sd O2 td t).

Definition sched_in_dom (sd: ossched) :=
  forall O td t, sd O td t -> sdom O t td.  
    
Definition sd_is_func (sd: ossched) := 
  forall O td t t', sd O td t -> sd O td t' -> t = t'. 

Record well_sched
  (aspc: osapispec) (ispc: osintspec) (sd: ossched) (dteq: dt_obeq_t) : Prop :=
  {
    ws_tick_equiv: tick_dt_equiv ispc dteq;
    ws_ntck_knl: no_tick_in_kfunc aspc;
    ws_tick_cdeq: tick_cdom_eq ispc dteq; 
    ws_tick_prsv_cd: tick_preserves_cdom ispc dteq; 
    ws_sched_inv: sched_inv sd;
    ws_sched_eqdom: sched_same_dom sd;
    ws_swi_dteq: swi_dteq dteq; 
    ws_sched_eqchoi: sched_same_choice sd dteq; 
    ws_sch_in_dom: sched_in_dom sd; 
    ws_sd_fn: sd_is_func sd
  }. 
    

Definition good_stmts (kspc: osspec) : Prop :=
  match kspc with
    (aspc, ispc, sd) =>
      (
        forall f r tp tl,
          aspc f = Some (r, (tp, tl)) ->
          forall vl, tl_vl_match tl vl = true -> ~exists vl', r vl = spec_done vl'
      )
      /\
        (forall i s, ispc i = Some s -> ~exists vl', s = spec_done vl')
  end.

Record good_dteq (dteq: dt_obeq_t) : Prop :=
  {
    gd_equiv_rel: forall d, Equivalence (dteq d);
    gd_tsd: tsk_same_dom dteq
  }. 

Inductive top_rule:
  rg_env_t -> rg_env_t -> rg_env_t -> rg_env_t -> flows_to_t -> dt_obeq_t -> (* uprogs_-> *) osspec -> Prop := 

  TopRule: 
    forall (* uprgs *) (ospc: osspec) aspc ispc sd rly_tsk guar_tsk rly_itp guar_itp dteq flt, 
      ospc = (aspc, ispc, sd) ->
      good_stmts ospc -> 
      well_rg rly_tsk guar_tsk rly_itp guar_itp ->
      well_sched aspc ispc sd dteq ->
      good_dteq dteq -> 
      (
        forall f tp tl vl acode t,
          aspc f = Some (acode, (tp, tl)) ->
          tl_vl_match tl vl = true ->
          ((forall O, I O -> head_sat t O (acode vl)) /\
             (exists q, deduct_rules t (rly_tsk t) (guar_tsk t) flt dteq (acode vl) q)) 
      ) ->
      (
        forall i s t,
          ispc i = Some s ->
          ((forall O, I O -> head_sat t O s) /\
             (exists q, deduct_rules t (rly_itp t) (guar_itp t) flt dteq s q)) 
      ) ->
      top_rule rly_tsk guar_tsk rly_itp guar_itp flt dteq (* uprgs *) ospc. 
    
End DeductRules.  
