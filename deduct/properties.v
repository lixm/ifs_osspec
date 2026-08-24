
Require Import memory.
Require Import language.
Require Import opsem.

Require Import rules. 


Section Properties.

Context {state_t : Type}.
Context `{State state_t}.

Inductive hpstep_star :
  uprogs_t -> osspec -> sys_config_t -> sys_config_t -> Prop :=

| hpstep_zero: forall uprg kspc cfg, 
    hpstep_star uprg kspc cfg cfg

| hpstep_more: forall uprg kspc cfg cfg' cfg'' T ust O T' ust' O' act,
    cfg = (T, ust, O) ->
    cfg' = (T', ust', O')-> 
    hpstep uprg kspc T ust O T' ust' O' act ->
    hpstep_star uprg kspc cfg' cfg'' ->
    hpstep_star uprg kspc cfg cfg''.  


Parameter cfg0: sys_config_t. 

Definition reachable
  (uprg: uprogs_t) (kspc: osspec) (init: sys_config_t -> Prop) cfg :=
  init cfg0 /\ hpstep_star uprg kspc cfg0 cfg. 
    
Definition prog_equiv (td: task_dom) (T1 T2: tasks) (O1 O2: state_t) :=
  forall t, sdom O1 t td -> sdom O2 t td -> T1 t = T2 t.

Definition ust_equiv (td: task_dom) (ust1 ust2: ustate) := 
  get ust1 td = get ust2 td. 

Definition same_cdom (O1 O2: state_t) :=
  forall cid td, cur_dom O1 cid td <-> cur_dom O2 cid td. 

Definition same_td_for_ct (O1 O2: state_t) := 
  forall cid,
    ((exists t, cur_tsk O1 cid t) <-> (exists t, cur_tsk O2 cid t)) /\ 
      forall t1 t2,
        cur_tsk O1 cid t1 ->
        cur_tsk O2 cid t2 ->
        (forall td, sdom O1 t1 td <-> sdom O2 t2 td). 

Definition ctid_equiv (td: task_dom) (O1 O2: state_t) :=
  forall cid t1 t2,
    cur_tsk O1 cid t1 ->
    cur_tsk O2 cid t2 -> 
    sdom O1 t1 td ->
    (* from obsr_equiv_schd we know "dom_of_tsk_ext t2 O2 td" *)
    t1 = t2.   

Definition obsr_equiv (d: dom) (dteq: dt_obeq_t) (cfg1 cfg2: sys_config_t) := 
  exists T1 ust1 O1 T2 ust2 O2,
    cfg1 = (T1, ust1, O1) /\
      cfg2 = (T2, ust2, O2) /\
      match d with
        TaskDom td =>
          prog_equiv td T1 T2 O1 O2 /\
            ust_equiv td ust1 ust2 /\ 
            ctid_equiv td O1 O2 /\  
            dteq (TaskDom td) O1 O2
      | SchedDom =>
          same_cdom O1 O2 /\ 
            same_td_for_ct O1 O2 /\ 
            dteq SchedDom O1 O2
      end. 


Definition confidentiality_u
  (flt: flows_to_t) (uprg: uprogs_t) (kspc: osspec) (init: sys_config_t -> Prop) (dteq: dt_obeq_t) :=  

  forall cfg1 cfg2 cfg1' cfg2' (d d1' d2': dom) ac,    
    reachable uprg kspc init cfg1 ->
    reachable uprg kspc init cfg2 ->
    obsr_equiv SchedDom dteq cfg1 cfg2 ->
    obsr_equiv d dteq cfg1 cfg2 ->    
    (flt d1' d -> obsr_equiv d1' dteq cfg1 cfg2) ->
    hpstep_d uprg kspc cfg1 cfg1' ac d1' ->
    hpstep_d uprg kspc cfg2 cfg2' ac d2' ->
    obsr_equiv d dteq cfg1' cfg2'.   

  
Definition integrity_u
  (flt: flows_to_t) (uprg: uprogs_t) (kspc: osspec) (init: sys_config_t -> Prop) (dteq: dt_obeq_t) :=

  forall cfg cfg' act d' d, 
    reachable uprg kspc init cfg ->
    hpstep_d uprg kspc cfg cfg' act d' ->
    ~flt d' d ->
    obsr_equiv d dteq cfg cfg'.  
  

End Properties. 
