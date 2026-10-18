
Require Import memory. 
Require Import language.
Require Import opsem.

Require Import state. 
Require Import specs_common. 


(************************************* OSTickISR *************************************)    

Inductive tickchange : 
  tid -> 
  taskstatus -> QueMod.map -> 
  taskstatus -> QueMod.map -> Prop:= 

| no_change: 
  forall t st qls eid,
    ((st = rdy) \/
      (st = wait (os_stat_qpend eid) None) \/
      (st = wait (os_stat_qpend eid) (Some Int.zero))) -> 
    tickchange t st qls st qls 

| wait_time_dec:
  forall t st qls st' qid n,
    st = wait (os_stat_qpend qid) (Some n) ->
    (Int.eq Int.one n = false /\ Int.eq Int.zero n = false) -> 
    st' = wait (os_stat_qpend qid) (Some (Int.sub n Int.one)) ->
    tickchange t st qls st' qls 

| wait_que_rdy: 
  forall t st qls qls' st' qid ms sz ts d,
    st = wait (os_stat_qpend qid) (Some Int.one) ->
    get qls qid = Some (msgq ms sz ts, d) ->     
    st' = rdy -> 
    qls' = set qls qid (msgq ms sz (remove_tid t ts), d) -> 
    tickchange t st qls st' qls'.


Inductive tickstep':
  task_dom ->   
  TcbMod.map -> QueMod.map -> 
  TcbMod.map -> QueMod.map -> 
  TcbMod.map -> Prop := 

| endtls_step :
  forall (td: task_dom) (tls:TcbMod.map) (qls : QueMod.map),
    tickstep' td tls qls tls qls emp 

| ext_step :
  forall
    (td: task_dom)
    (tls tls' tls'' : TcbMod.map) (qls qls' qls'': QueMod.map) (t : tidspec.A) 
    (p : priority) (st st' : taskstatus) (msg0 : msg) (sus0 : sus_st) tls_used tls_used',
    
    joinsig t (p, st, msg0, sus0, td) tls_used' tls_used ->
    tickchange t st qls st' qls' -> 
    set tls t (p, st', msg0, sus0, td) = tls' ->
    tickstep' td tls' qls' tls'' qls'' tls_used' -> 
    tickstep' td tls qls tls'' qls'' tls_used

| ext_step_no_change :
  forall td p st msg0 sus0 td' tls_used' tls_used tls qls tls' qls' t, 
    joinsig t (p, st, msg0, sus0, td') tls_used' tls_used ->
    td' <> td ->
    tickstep' td tls qls tls' qls' tls_used' -> 
    tickstep' td tls qls tls' qls' tls_used.  
  

Definition tickstep td tls qls tls' qls' := tickstep' td tls qls tls' qls' tls. 


Definition tickisr_spec (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match rst with
    (vl', O') =>
      exists tls qls ctid dtmp dt cdmp cd cid,
      get O coretid = Some (oscoret ctid) /\
        get ctid cid = Some t /\ (* the task t is current task on core cid *) 
        get O abstcblsid = Some (abstcblist tls) /\ 
        get O quelsid = Some (absecblist qls) /\
        get O domtimeid = Some (domtime dtmp) /\ 
        get dtmp cid = Some dt /\ 
        get O curdomid = Some (curdom cdmp) /\
        get cdmp cid = Some cd /\ 
        ac = _TickAct cid /\ 
        let dt' := Int.sub dt Int.one in
        (* update remaining time for the current dom on the current core *) 
        let O_ := set O domtimeid (domtime (set dtmp cid dt')) in
        exists tls' qls',
          
          tickstep cd tls qls tls' qls' /\
            
            let O__ := set (set O_ abstcblsid (abstcblist tls')) quelsid (absecblist qls') in  
            if Int.eq dt' Int.zero then (* domain switch *)
              exists idxmp lenmp ldmp schdmp, 
              exists idx len ld schd,  
                get O dschedidxid = Some (dschedidx idxmp) /\
                  get idxmp cid = Some idx /\ 
                  get O dschedlenid = Some (dschedlen lenmp) /\
                  get lenmp cid = Some len /\ 

                  get O lastdomid = Some (lastdom ldmp) /\
                  get ldmp cid = Some ld /\
                  get O dschedid = Some (dsched schdmp) /\
                  get schdmp cid = Some schd /\
                  let idx' := if (Int.ltu (Int.add idx Int.one) len) then (Int.add idx Int.one) else Int.zero in
                  match get schd idx' with
                  | Some (dom, schd_len) =>
                      let O1 := set O__ dschedidxid (dschedidx (set idxmp cid idx')) in
                      let O2 := set O1 lastdomid (lastdom (set ldmp cid cd)) in 
                      let O3 := set O2 curdomid (curdom (set cdmp cid dom)) in
                      let O4 := set O3 domtimeid (domtime (set dtmp cid schd_len)) in
                      O' = O4 /\ vl' = nil 
                  | _ => O' = O /\ vl' = Vint32 (Int.repr OS_ERR_NO_DSCH_CELL) :: nil 
                  end
            else (* no domain switch *) 
              O' = set O__ domtimeid (domtime (set dtmp cid dt')) /\ vl' = nil 
  end.

Definition tickisr : spec_code := tickisr_spec (|nil|);; sched trivial_asrt;; spec_done nil.  
  
