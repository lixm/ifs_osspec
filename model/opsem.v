
Require Import memory. 
Require Import language.
Require Import Coq.Logic.FunctionalExtensionality.

Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.

Definition OSTCBHighRdy:= 59%Z.
Definition OSTCBCur:=60%Z.

Definition vtoZ (v:val):option Z:=
  match v with
    | Vint32 a => Some (Int.unsigned a)
    |_=>None
  end.

(* modified by zhanghui*)
Open Scope Z_scope.
Definition type_val_match (t:type) (v:val) :=
  match t,v with
  | Tnull, Vnull => true
  | Tptr t, Vnull => true
  | Tcom_ptr id,Vnull => true
  | Tint8,Vint32 v => (*if v is in the range of Tint8 return True, if not return False*)
      match (Int.unsigned v) <=? Byte.max_unsigned with
      | true => true
      | false => false
      end
  | Tint16,Vint32 v => (*if v is in the range of Tint16 return True, if not return False*)
      match (Int.unsigned v) <=? Int16.max_unsigned with
      | true => true
      | false => false
      end
  | Tint32,Vint32 v =>true
  | Tptr t,Vptr l => true
  | Tcom_ptr id,Vptr l => true
  | Tarray _ _, _ => true
  | Tstruct _ _, _ =>true
  | _,_=> false
  end.

Fixpoint tl_vl_match (tl:typelist) (vl:vallist) :=
  match tl with 
  | nil => 
      match vl with 
      | nil => true
      | _ => false
      end
  | t :: tl' => 
      match vl with
      | v :: vl' => if type_val_match t v then tl_vl_match tl' vl' else false
      | _ => false
      end
  end.  

(****)
(* Definition eqdomtls (tls tls':TcbMod.map) := *)
(*   forall tid, indom tls tid <-> indom tls' tid. *)
    
(* Definition dom_impl (O O': osabst) := *)
(*   forall (x: absdataid), *)
(*     match get O x with *)
(*       Some (abstcblist _) => exists y, get O' x = Some (abstcblist y) *)
(*     | Some (absecblist _) => exists y, get O' x = Some (absecblist y) *)
(*     | Some (chanlist _) => exists y, get O' x = Some (chanlist y)  *)
(*     | Some (freetidlist _) => exists y, get O' x = Some (freetidlist y) *)
(*     | Some (freeqidlist _) => exists y, get O' x = Some (freeqidlist y)  *)
(*     | Some (ostm _) => exists y, get O' x = Some (ostm y) *)
(*     | Some (oscoret _) => exists y, get O' x = Some (oscoret y)  *)
(*     | Some (tskctrlst _) => exists y, get O' x = Some (tskctrlst y)  *)
(*     | Some (dschedidx _) => exists y, get O' x = Some (dschedidx y) *)
(*     | Some (dschedlen _) => exists y, get O' x = Some (dschedlen y)  *)
(*     | Some (curdom _) => exists y, get O' x = Some (curdom y)  *)
(*     | Some (lastdom _) => exists y, get O' x = Some (lastdom y)  *)
(*     | Some (domtime _) => exists y, get O' x = Some (domtime y)   *)
(*     | Some (dsched _) => exists y, get O' x = Some (dsched y)  *)
(*     | None => get O' x = None *)
(*     end. *)

(* Definition eqdomO0 O O' := *)
(*   dom_impl O O' /\ dom_impl O' O. *)

(* Definition eqdom_tls O O' :=  *)
(*   forall tls, *)
(*     get O abstcblsid = Some (abstcblist tls) -> *)
(*     exists tls',  get O' abstcblsid = Some (abstcblist tls') /\ eqdomtls tls tls'.  *)

(* Definition eqdomO (O O': osabst) := eqdomO0 O O' /\ eqdom_tls O O'.  *)

(* (* O and O' agree on the current task for each core *)  *)
(* Definition tidsame (O O':osabst) := *)
(*   get O coretid = get O' coretid. *)

(* Definition dom_rel_t := tid -> osabst -> task_dom -> Prop.  *)

Inductive spec_step `{State}:
  ossched -> tid -> spec_code -> state_t -> spec_code -> state_t -> sem_act -> Prop := 

| spec_prim_step:
  forall sc t O O' (step:osabstep) vl vl' act asrt,
    step t vl O act (vl', O') ->
    (forall cid t, cur_tsk O cid t <-> cur_tsk O' cid t) -> 
    (forall cid td, cur_dom O cid td <-> cur_dom O' cid td) -> 
    (* the above condition can be examined in a refinement verification *) 
    (* eqdomO0 O O' -> *) 
    (* (((~exists t fp argp, act = _TCreAct t fp argp) /\ (~exists t, act = _TDelAct t)) *)
    (*  -> eqdom_tls O O') ->   *)
    (* tidsame O O' -> *) 
    (* join O Of OO -> *)
    (* join O' Of OO' -> *)
    spec_step sc t (spec_prim asrt vl step) O (spec_done vl') O' act

| spec_sched_step:
  forall (sc:ossched) t cid td (O: state_t) asrt,
    (* get O coretid = Some (oscoret ct) -> *)
    (* get ct cid = Some t ->  *)
    (* sdom O t td ->  *)
    cur_tsk O cid t -> 
    cur_dom O cid td -> 
    sc O td t -> 
    (* join O Of OO -> *)
    spec_step sc t (sched asrt) O (spec_done nil) O _TauAct 

| spec_seq_step_end:
  forall t vl s1 vs2 O O' sc act,
    spec_step sc t s1 O (spec_done vl) O' act ->
    spec_step sc t (spec_seq s1 vs2) O (vs2 vl) O' act

| spec_seq_step_cont:
  forall t O O' s1 s2 s1' sc act,
    spec_step sc t s1 O s1' O' act ->
    (~exists vl, s1' = spec_done vl) -> 
    spec_step sc t (spec_seq s1 s2) O (spec_seq s1' s2) O' act

(* | spec_case_step: *)
(*   forall sc t asrt ss O s O' s' act, *)
(*     ss O = s -> *)
(*     spec_step sc t s O s' O' act -> *)
(*     spec_step sc t (spec_case asrt ss) O s' O' act *)

| spec_dowh_step:
  forall sc t s b O, 
    spec_step sc t (spec_dowh s b) O
      (spec_seq s (fun vl => if b vl then (spec_dowh s b) else spec_done vl)) O _TauAct. 

(* | spec_assume_step: *)
(*   forall O Of (B: abs_cond) OO sc t,  *)
(*     B O -> *)
(*     join O Of OO -> *)
(*     spec_step sc t (spec_assume B)  OO  (spec_done nil) OO KTauAct *)

(* | spec_atom_step_done: *)
(*   forall sc t cd O O' vl act,  *)
(*     spec_step sc t cd O (spec_done vl) O' act -> *)
(*     spec_step sc t (spec_atom cd) O (spec_done vl) O' act *)

(* | spec_atm_step_cont: *)
(*   forall sc t cd cd' O O' O'' vl act0 act,  *)
(*     spec_step sc t cd O cd' O' act0 -> *)
(*     ((~exists vl, cd' = spec_done vl)) ->  *)
(*     spec_step sc t (spec_atom cd') O' (spec_done vl) O'' act ->  *)
(*     spec_step sc t (spec_atom cd) O (spec_done vl) O'' act *)


Inductive hapistep `{State}: 
  osspec -> tid ->
  code -> strat_state_t -> state_t -> code -> strat_state_t -> state_t -> sem_act -> Prop := 

| hapienter_step:
  forall (A :osspec) (B:osapispec) (C:osintspec) (D: ossched) (O:state_t) (cd cd':code)
         (ks:cont) (f:fid) (vl:vallist) r tl tp t strat stt stt',
    A = (B, C, D) ->
    cd = (cur_strat strat, kstop) -> 
    strat stt Vundef = (_CallAct f vl, stt') ->
    B f = Some (r, (tp,tl)) -> 
    tl_vl_match tl vl = true ->
    cd' = (cur_stmt (r vl), kenknl f strat kstop) ->  
    hapistep A t cd stt O cd' stt' O (_CallAct f vl)
                
| hidapi_step :
    forall (A :osspec) (O O':state_t) ks cd cd' ac t stt,
      spec_step (snd A) t cd O cd' O' ac ->
      (~exists f vl, ac = _CallAct f vl) -> 
      hapistep A t (cur_stmt cd, ks) stt O (cur_stmt cd', ks) stt O' ac 

| hapiexit_step :
  forall (A :osspec) (O:state_t) ks vl t strat stt stt' ac f,
    (* here we express that there is no interrupt handling in the continuation *)
    (* this makes the semantics deterministic given the existence of hintex_step *) 
    strat stt (match vl with nil => Vundef | v :: _ => v end) = (ac, stt') -> 
    hapistep A t
      (cur_stmt (spec_done vl), kenknl f strat ks) stt O
      (cur_strat strat, ks) stt' O _TauAct
               
| hintex_step:
  forall (A :osspec) ks O c t stt i, 
    hapistep A t
      (cur_stmt (spec_done nil), kevent i c ks) stt O
      (c, ks) stt O _TauAct.


Inductive htstep `{State}: 
  osspec -> tid -> 
  code -> strat_state_t -> state_t -> code -> strat_state_t -> state_t -> 
  sem_act -> Prop := 
  
| htclt_step : 
  forall (A: osspec) c t (O: state_t) strat ks stt stt' ac, 
    c = (cur_strat strat, ks) -> 
    strat stt Vundef = (ac, stt') ->
    (~exists f vl, ac = _CallAct f vl) -> 
    htstep A t c stt O c stt' O _TauAct

| hapi_step :
  forall (A: osspec) (O O': state_t) (c c': code) (strat: strat_t) stt stt' t ac, 
    hapistep A t c stt O c' stt' O' ac -> 
    htstep A t c stt O c' stt' O' ac.  


(* The original rule abstracted away the requirement that an
    interrupt at the same level should not be already in service. 
    We capture this condition using "absintcont ks = None" since the
    only interrupt in the system (for information flow verification) is
    the tick interrupt. *)  
Inductive htistep `{State}: osintspec -> code  -> state_t -> code  -> state_t -> hid -> Prop :=
| hinten_step:
  forall  (ispc: osintspec)  (O: state_t) c ks (i: hid) l,
    ispc i = Some l ->
    (* intcont ks = None ->  *) 
    htistep ispc (c, ks) O (cur_stmt l, kevent i c ks) O i.

(* Definition tdom_mp := tid -> osabst -> task_dom. *)

Inductive sec_act : Type := 
  TauAct (cid: coreid) | EniAct (cid: coreid) (i: nat) | TickAct (cid: coreid) | SwAct (cid: coreid) (* | APIAct (f: fid) *).   

Definition action := prod sec_act tid. 

Definition upd_task_pool `{State} (T: tasks) t C :=
  fun t' => if beq_tid t t' then Some C else T t'.

Lemma beq_tid_true : forall t, beq_tid t t = true.
Proof.
  intros.
  unfolds; destruct t.
  rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_refl.
  rewrite Int.eq_true.
  simpl; auto.
Qed.

Lemma beq_tid_true_eq: forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H; destruct t1; destruct t2.
  apply andb_true_iff in H; destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Pos.eqb_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.

Lemma upd_task_pool_eq `{State} :
  forall T t C, upd_task_pool T t C t = Some C.
Proof.
  intros.
  unfolds.
  rewrite beq_tid_true.
  auto.
Qed.

Lemma upd_task_pool_neq `{State} :
  forall T t t' C, t <> t' -> (upd_task_pool T t C) t' = T t'.
Proof.
  introv Hneq.
  unfolds.
  destruct (beq_tid t t') eqn: E.
  -
    apply beq_tid_true_eq in E. false.
  -
    auto.
Qed. 
             
Inductive hpstep `{State}: 
  uprogs_t -> osspec -> 
  tasks -> ustate -> state_t -> tasks -> ustate -> state_t -> action -> Prop :=  
  
| hp_step:
  forall u (p: osspec) (T T': tasks) (O O': state_t) (C C': code) (t: tid) _act
         (ust: ustate) (sst sst': strat_state_t) cid d (act: sec_act),  
    (* get O coretid = Some (oscoret ct) -> *)
    (* get ct cid = Some t ->     *)
    cur_tsk O cid t -> 
    sdom O t d -> 
    get ust d = Some sst -> 
    htstep p t C sst O C' sst' O' _act -> 
    (~exists t fp argp, _act = _TCreAct t fp argp) ->
    (~exists t, _act = _TDelAct t) ->
    (_act = _TickAct cid /\ act = TickAct cid \/
       (_act = _TauAct \/ exists f vl, _act = _CallAct f vl) /\ act = TauAct cid) ->  
    T t = Some C ->
    T' = upd_task_pool T t C' -> 
    hpstep u p T ust O T' (set ust d sst') O' (act, t)
                    
| hi_step :
  forall u (p: osspec) A ispec B  (T T': tasks) (O O': state_t) ust (C C': code) (t: tid) i cid, 
    p = (A, ispec, B) -> 
    (* get O coretid = Some (oscoret ct) -> *)
    (* get ct cid = Some t ->  *)
    cur_tsk O cid t -> 
    T t = Some C -> 
    T' = upd_task_pool T t C' -> 
    htistep ispec C O C' O' i ->
    hpstep u p T ust O T' ust O' (EniAct cid i, t)
                     
| hswi_step :
  forall u td (p: osspec) A B sd cid (T T': tasks) ust (O O': state_t) (t t': tid) C ks vs asrt,
    p = (A, B, sd) ->  
    (* get O coretid = Some (oscoret ct) -> *)
    (* get ct cid = Some t -> *)
    cur_tsk O cid t ->
    cur_dom O cid td -> 
    (* get O curdomid = Some (curdom cdmp) ->  *)
    (* get cdmp cid = Some td ->  *)
    (* immediately after a domain switch,
        the current domain will not be the same as the domain of the current task *)  
    sd O td t' -> 
    (* context switch within the domain td, capturing intra-domain scheduling *)
    upd_cur_tsk O cid t' O' ->  
    (* O' = set O coretid (oscoret (set ct cid t')) ->  *)
    T t = Some C ->
    C = (cur_stmt (spec_seq (sched asrt) vs), ks) -> 
    T' = upd_task_pool T t (cur_stmt (vs nil), ks) ->  
    hpstep u p T ust O T' ust O' (SwAct cid, t) 
           
| hpcrt_step :
  forall u (T T': tasks) (O O': state_t) (t t': tid)
         (p: osspec) (tau: type) (d1 d2: decllist)
         (C C': code) cid fp argp valstr strat ust sst _ac td, 

    (* get O coretid = Some (oscoret ct) -> *)
    (* get ct cid = Some t ->  *)
    cur_tsk O cid t -> 
    T t = Some C -> 
    sdom O t td ->
    get ust td = Some sst -> 
    htstep p t C sst O C' sst O' _ac -> 
    _ac = _TCreAct t' fp argp ->
    get u fp = Some valstr -> 
    valstr (Vptr argp) = strat ->     
    T' = upd_task_pool (upd_task_pool T t C') t' (cur_strat strat, kstop) -> 

    hpstep u p T ust O T' ust O' (TauAct cid, t)

    (* get O abstcblsid = Some (abstcblist tls) -> *)
    (* get tls t = Some (v_, st_, m_, sus_, d) ->  *)
    (* set O abstcblsid (abstcblist tls') = O' -> *)
    (* join tls (sig t' (v, rdy, Vnull, false, d)) tls' -> *)
      
| hpdel_step:
  forall u p T T' t t' C C' O O' ust sst _ac cid td,   

    (* get O coretid = Some (oscoret ct) -> *)
    (* get ct cid = Some t ->  *)
    cur_tsk O cid t ->    
    T t = Some C ->
    sdom O t td ->
    get ust td = Some sst -> 
    htstep p t C sst O C' sst O' _ac -> 
    _ac = _TDelAct t' -> 
    T' = upd_task_pool T t C' ->

    hpstep u p T ust O T' ust O' (TauAct cid, t).   

    (* get O abstcblsid = Some (abstcblist tls) -> *)
    (* set O abstcblsid (abstcblist tls') = O' -> *)
    (* get tls t' = Some (prio, st, msg, sus, d) -> *)
    (* join tls' (sig t' (prio, st, msg, sus, d)) tls -> *) 


(* Definition in_intr (T: tasks) (O: osabst) : Prop := *)
(*   exists c ke ks, *)
(*     code_cur_task T O = Some (c, (ke, ks)) /\ absintcont ks <> None. *)

(* Definition dom_mp := action -> osabst -> dom.   *)

Definition sys_config_t `{State} := (tasks * ustate * state_t)%type. 

Inductive dom : Type :=
| TaskDom (i : task_dom) 
| SchedDom
.

Inductive hpstep_d `{State}: 
  uprogs_t -> osspec -> 
  sys_config_t -> sys_config_t ->   
  sec_act -> dom -> Prop :=

  hp_step_dom:
    forall u hp T ust O T' ust' O' act ac t td,
      hpstep u hp T ust O T' ust' O' act ->
      act = (ac, t) -> 
      (~exists cid, ac = TickAct cid) ->
      (~exists cid, ac = SwAct cid) -> 
      sdom O t td -> 
      hpstep_d u hp (T, ust, O) (T', ust', O') ac (TaskDom td) 

| hp_sched_dom:
    forall u hp T ust O T' ust' O' act ac t cid,
      hpstep u hp T ust O T' ust' O' act ->
      act = (ac, t) -> 
      (ac = TickAct cid \/ ac = SwAct cid) -> 
      hpstep_d u hp (T, ust, O) (T', ust', O') ac SchedDom.   
  

      
