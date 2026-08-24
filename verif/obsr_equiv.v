
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import state. 
Require Import specs_common.


Definition dom_of_tsk (t: tid) (O: osabst) : option task_dom :=
  match get O abstcblsid with
    Some (abstcblist tls) =>
      match get tls t with
        Some (pr, st, msg, sus, d) => Some d
      | _ => None
      end
  | _ => None
  end.

Definition ex_tsk_in_dom (t: tid) (td: task_dom) (tls: TcbMod.map) :=
  exists pr st m (* cm  *)sus, get tls t = Some (pr, st, m, (* cm,  *)sus, td).   

Definition obsr_equiv_tasks (td: task_dom) (O1 O2: osabst) :=
  ((exists tls, get O1 abstcblsid = Some (abstcblist tls)) <->
     (exists tls, get O2 abstcblsid = Some (abstcblist tls)))
  /\
    forall tls1 tls2 t, 
      get O1 abstcblsid = Some (abstcblist tls1) -> 
      get O2 abstcblsid = Some (abstcblist tls2) -> 
      ((ex_tsk_in_dom t td tls1 <-> ex_tsk_in_dom t td tls2) 
       /\ (forall pr1 pr2 st1 st2 msg1 msg2 (* cm1 cm2  *)sus1 sus2 d1 d2,
              get tls1 t = Some (pr1, st1, msg1, (* cm1,  *)sus1, d1) ->
              get tls2 t = Some (pr2, st2, msg2, (* cm2,  *)sus2, d2) ->
              ((* (d1 = td <-> d2 = td) /\ *)
                (d1 = td -> (pr1 = pr2 /\ st1 = st2 /\ msg1 = msg2 /\ sus1 = sus2))))).  

Definition ex_mq_in_dom (q: qid) (td: task_dom) (qls: QueMod.map) :=
  exists ms sz ts, get qls q = Some (msgq ms sz ts, td).  

Definition obsr_equiv_mqs (td: task_dom) (O1 O2: osabst) :=
  ((exists qls, get O1 quelsid = Some (absecblist qls)) <->
     (exists qls, get O2 quelsid = Some (absecblist qls)))
  /\
    forall qls1 qls2 q,
      get O1 quelsid = Some (absecblist qls1) -> 
      get O2 quelsid = Some (absecblist qls2) ->     
      ((ex_mq_in_dom q td qls1 <-> ex_mq_in_dom q td qls2) 
       /\ (forall mq1 mq2 d1 d2, 
              get qls1 q = Some (mq1, d1) ->
              get qls2 q = Some (mq2, d2) ->
              ((* (d1 = td <-> d2 = td) /\  *)(d1 = td -> mq1 = mq2)))). 

(* 1. channels belong to dest dom *)
(* 2. because there is no dynamic creation/deletion of channels, *)
(*     there is no need to express *)
(*     "there is a chan in td for O1 iff there is a chan in td for O2" *)
Definition obsr_equiv_chans (td: task_dom) (O1 O2: osabst) :=
  ((exists chls, get O1 chlsid = Some (chanlist chls)) <->
     (exists chls, get O2 chlsid = Some (chanlist chls)))
  /\
    forall chs1 chs2 chid, 
      get O1 chlsid = Some (chanlist chs1) -> 
      get O2 chlsid = Some (chanlist chs2) -> 
      ((get chs1 chid <> None <-> get chs2 chid <> None)
       /\ (forall sd1 sd2 dd1 dd2 c1 c2,
              get chs1 chid = Some (sd1, dd1, c1) ->
              get chs2 chid = Some (sd2, dd2, c2) -> 
              ((* (dd1 = td <-> dd2 = td) /\ *)
                sd1 = sd2 /\ dd1 = dd2 /\ 
                 (dd1 = td -> ((* sd1 = sd2 /\  *)c1 = c2))))).  

Definition obsr_equiv_freetids (td: task_dom) (O1 O2: osabst) :=
  ((exists fts, get O1 freetid = Some (freetidlist fts)) <->
     (exists fts, get O2 freetid = Some (freetidlist fts)))
  /\
    forall fts1 fts2 ts, 
      get O1 freetid = Some (freetidlist fts1) ->
      get O2 freetid = Some (freetidlist fts2) -> 
      (get fts1 td = Some ts <-> get fts2 td = Some ts). 

Definition obsr_equiv_freeqids (td: task_dom) (O1 O2: osabst) :=
  ((exists fqs, get O1 freeqid = Some (freeqidlist fqs)) <->
     (exists fqs, get O2 freeqid = Some (freeqidlist fqs)))
  /\
    forall fqs1 fqs2 qs, 
      get O1 freeqid = Some (freeqidlist fqs1) -> 
      get O2 freeqid = Some (freeqidlist fqs2) -> 
      get fqs1 td = Some qs <-> get fqs2 td = Some qs. 

Record obsr_equiv_tskd (td: task_dom) (O1 O2: osabst) :=
  {
    oe_td_tasks: obsr_equiv_tasks td O1 O2;
    oe_td_mqs: obsr_equiv_mqs td O1 O2;
    oe_td_chs: obsr_equiv_chans td O1 O2;
    oe_td_fts: obsr_equiv_freetids td O1 O2;
    oe_td_fqs: obsr_equiv_freeqids td O1 O2
  }.

Record obsr_equiv_schd (O1 O2: osabst) :=
  {
    oe_sch_cd_eq: get O1 curdomid = get O2 curdomid;
    oe_sch_dschlen_eq: get O1 dschedlenid = get O2 dschedlenid;
    oe_sch_dschidx_eq: get O1 dschedidxid = get O2 dschedidxid;
    oe_sch_dschtbl_eq: get O1 dschedid = get O2 dschedid;
    oe_sch_dtm_eq: get O1 domtimeid = get O2 domtimeid
  }.
    
Definition obsr_equiv_data (d: dom) (O1 O2: osabst) :=
  match d with
    TaskDom td => obsr_equiv_tskd td O1 O2 
  | SchedDom => obsr_equiv_schd O1 O2
  end.

