
Require Import Integers.
Require Import memory. 
Require Import language.
Require Import opsem.

Require Import state. 
Require Import specs_common. 

Definition blocked: val := Vint32 Int.mone. 

Definition dom_chk_ok: int := Int.repr (-11). 
Definition dom_chk_err: int := Int.repr (-12).
  
Definition tsk_mq_same_dom (* (q: qid) *) (vl: vallist) (t: tid) (O: osabst) : Prop :=
  match vl with
  | Vptr q :: _ => exists td, sdom_ O t td /\ q_sdom_ O q td
  | _ => True
  end.

Definition mq_check_dom (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match rst with
    (vl', O') =>
      match vl with
        Vnull :: _ => err_prop OS_ERR_PEVENT_NULL vl' O O' ac
      | Vptr qid :: _ => 
          exists tls prio st msg (* chm  *)sus td qls,
          get O abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio, st, msg, (* chm,  *)sus, td) /\ 
            get O quelsid = Some (absecblist qls) /\
            match get qls qid with
            | Some (msgq ms y ts, dm) =>
                (td = dm /\ vl' = Vint32 dom_chk_ok :: nil
                 \/ td <> dm /\ vl' = Vint32 dom_chk_err :: nil) /\   
                  O' = O /\ 
                  ac = _TauAct 
            (* get O tskctrlstid = Some (tskctrlst tcst) /\ *)
            (* O' = set O tskctrlstid (tskctrlst (set tcst t (qpend_id, vl))) *)
            | _ => vl' = Vint32 dom_chk_err :: nil /\ O' = O /\ ac = _TauAct
            end
      | _ => err_prop MODEL_ERR_PARAMS vl' O O' ac
      end
  end.

(************************************* OSQPend *************************************) 

  
Definition qpend_before_sched (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match rst with
    (vl', O') =>
      exists qid v qls tls, 
      vl = Vptr qid :: Vint32 v :: nil /\
        get O quelsid = Some (absecblist qls) /\        
        match get qls qid with 
        | Some (msgq ms y ts, dm) => 
            get O abstcblsid = Some (abstcblist tls) /\
              exists prio st msg (* chm  *)sus td, 
                get tls t = Some (prio, rdy, msg, (* chm,  *)sus, td) /\ 
                  if negb (Int.eq_dec prio (Int.repr OS_IDLE_PRIO)) then
                    err_prop OS_ERR_IDLE_PRIO vl' O O' ac
                  else
                    match ms with
                      m :: ms' =>
                        st = rdy /\ 
                          (O' =
                             let qls' :=set qls qid (msgq ms' y ts, dm) in 
                             let tls' := set tls t (prio, rdy, msg, (* chm,  *)sus, td) in  
                             set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) /\
                          ac = _TauAct /\
                          vl' = Vint32 (Int.repr OS_NO_ERROR) :: m :: nil
                    | _ => 
                        (O' =
                           let qls' := set qls qid (msgq nil y (t::ts), dm) in
                           let tls' := set tls t (prio, wait (os_stat_qpend qid) (Some v), Vnull, (* chm,  *)sus, td) in 
                           set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) /\ 
                          ac = _TauAct /\
                          vl' = blocked :: nil 
                    end
        | _ => err_prop OS_ERR_NO_QUE_IN_DOM vl' O O' ac
        end
  end.  
    
Definition qpend_after_sched (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match rst with
    (vl', O') =>
      exists tls prio st msg (* chm  *)sus td,
      get O abstcblsid = Some (abstcblist tls) /\ 
        get tls t = Some (prio, st, msg, (* chm,  *)sus, td) /\ 
        match msg with          
        | Vptr _ =>
            let tls' := set tls t (prio, st, Vnull, (* chm,  *)sus, td) in 
            O' = set O abstcblsid (abstcblist tls') /\ vl' = msg :: nil /\ ac = _TauAct
        | _ =>
            vl' = Vnull :: nil /\ O' = O /\ ac = _TauAct  
        end
  end.
      
Definition qpend (vl:vallist) : spec_code :=
  mq_check_dom (| vl |) ;;>
    (fun vl' =>
       match vl' with
       | Vint32 i :: nil =>
           if Int.eq i dom_chk_ok then 
             (tsk_mq_same_dom vl) # qpend_before_sched [| vl |]
               ;;>
               (fun vl' =>
                  match vl' with
                  | (Vint32 ierr) :: vl'' =>
                      if Int.eq ierr Int.zero then (* OS_NO_ERROR *)
                        spec_done vl''
                      else
                        if Int.eq ierr Int.mone then 
                          sched trivial_asrt ;; qpend_after_sched (| nil |)
                        else
                          spec_done (Vnull :: nil) 
                  | _ => spec_skip_step (| nil |)  (* impossible branch *) 
                  end)
           else
             spec_done (Vnull :: nil)
       | _ => spec_done nil (* impossible case *) 
       end). 

Definition qpend_api := (qpend, (Tptr Tvoid, Tptr Tvoid :: Tint16 :: nil)). 


(************************************* OSQPost *************************************) 

Definition qpost_before_sched (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match rst with
    (vl', O') => 
      exists msg qid,
      vl = Vptr qid :: msg :: nil /\
        match msg with
        | Vptr m =>
            exists qls, 
            get O quelsid = Some (absecblist qls) /\
              match get qls qid with 
              | Some (msgq ml n ts, dm) => 
                  if Z.ltb (Z_of_nat (length ml)) (Int.unsigned n) then
                    match ts with
                    | nil =>
                        O' = (set O quelsid (absecblist (set qls qid (msgq (ml++(msg::nil)) n nil, dm)))) /\
                        vl' = Vint32 (Int.repr NO_ERR) :: nil /\ ac = _TauAct   
                    | _ =>
                        exists tls t' p st m (* cm  *)sus td, 
                        get O abstcblsid = Some (abstcblist tls) /\ 
                          GetHWait tls ts t' /\
                          get tls t' = Some (p, st, m, (* cm,  *)sus, td) /\ 
                          O' =
                            (let tls' := set tls t' (p, rdy, msg(* message sent*), (* cm,  *)sus, td) in 
                             let qls' := set qls qid (msgq ml n (remove_tid t' ts), dm) in
                             set (set O abstcblsid (abstcblist tls')) quelsid (absecblist qls')) /\
                          vl' = Vint32 (Int.repr NO_ERR) :: nil /\ ac = _TauAct 
                    end
                  else
                    err_prop MSGQ_OVF_ERR vl' O O' ac 
              | _ => err_prop OS_ERR_NO_QUE_IN_DOM vl' O O' ac
              end
        | _ => err_prop OS_ERR_INVALID_MSG vl' O O' ac
        end
  end.
       
Definition qpost (vl:vallist): spec_code :=
  mq_check_dom (| vl |) ;;>
    (fun vl' =>
       match vl' with
       | Vint32 i :: nil =>
           if Int.eq i dom_chk_ok then 
             (tsk_mq_same_dom vl) # qpost_before_sched [|vl|];; 
             sched trivial_asrt;;
             spec_done (Vint32 (Int.repr NO_ERR) :: nil)
           else
             if Int.eq i dom_chk_err then
               spec_done (Vint32 (Int.repr OS_ERR_NO_QUE_IN_DOM) :: nil)
             else
               spec_done vl'
       | _ => spec_done nil (* impossible case *) 
       end). 
         
Definition qpost_api := (qpost, (Tint8, Tptr Tvoid :: Tptr Tvoid :: nil)). 

