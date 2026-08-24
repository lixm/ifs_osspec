
Require Import Integers.
Require Import memory. 
Require Import language.
Require Import opsem.

Require Import state. 
Require Import specs_common. 

Definition cont := Vint32 Int.mone.


(************************************* OSTaskCreate *************************************)  

Definition taskcre_tcb_alloc (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match vl with
    Vptr fn :: Vptr arg :: Vint32 pr :: nil =>
      match rst with
        (vl', O') =>
          if Int.lt (Int.repr OS_LOWEST_PRIO) pr then
            err_prop OS_ERR_PRIO_INVALID (fst rst) O (snd rst) ac
          else
            exists tls pr_c st_c msg_c (* chm_c  *)sus_c d_c ts, 
              get O abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (pr_c, st_c, msg_c, (* chm_c,  *)sus_c, d_c) /\
                (
                  (
                    (exists t' st msg (* chm  *)sus, get tls t' = Some (pr, st, msg, (* chm,  *)sus, d_c)) /\  
                      err_prop OS_ERR_PRIO_EXIST_IN_DOM vl' O O' ac
                  )
                  \/
                    (~(exists t' st msg (* chm  *)sus, get tls t' = Some (pr, st, msg, (* chm,  *)sus, d_c)) /\ 
                       exists tsmp, 
                        get O freetid = Some (freetidlist tsmp) /\ 
                          get tsmp d_c = Some ts /\
                          match ts with
                            t_n :: ts' =>
                              ~In t_n ts' /\ 
                                O' = set (set O abstcblsid (abstcblist (set tls t_n (pr, rdy, Vnull, (* Vnull, *) false, d_c))))
                                       freetid (freetidlist (set tsmp d_c ts')) /\ 
                                ac = _TCreAct t_n fn arg /\ vl' = cont :: Vptr t_n :: nil 
                          | nil => err_prop OS_ERR_NO_MORE_TCB vl' O O' ac
                          end
                    )
                )
      end
  | _ => err_prop MODEL_ERR_PARAMS (fst rst) O (snd rst) ac
  end.

Definition taskcre (vl:vallist) : spec_code :=
  taskcre_tcb_alloc (| vl |)
    ;;>
    (fun vl' =>
       match vl' with
         (Vint32 ierr) :: vl'' =>
           if Int.eq ierr Int.mone then
             sched trivial_asrt ;;
             spec_done vl''
           else
             spec_done (Vnull :: nil)
       | _ => spec_skip_step (| nil |)
       end).

Definition taskcre_api := (taskcre, (Tptr Tvoid, Tptr Tvoid :: Tptr Tvoid :: Tint8 :: nil)). 


(************************************* OSTaskDel *************************************)   

Definition task_del_tcb_release (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match vl with
    Vint32 pr :: nil =>
      match rst with
        (vl', O') =>
          if Int.eq pr (Int.repr OS_IDLE_PRIO) then
            err_prop OS_ERR_DEL_IDLE vl' O O' ac
          else
            if Int.lt (Int.repr OS_LOWEST_PRIO) pr then
              err_prop OS_ERR_PRIO_INVALID vl' O O' ac
            else
              exists tls pr_c st_c msg_c (* chm_c  *)sus_c d_c,
                get O abstcblsid = Some (abstcblist tls) /\ 
                  get tls t = Some (pr_c, st_c, msg_c, (* chm_c, *) sus_c, d_c) /\
                  (
                    (
                      ~(exists t' st msg (* chm  *)sus, get tls t' = Some (pr, st, msg, (* chm,  *)sus, d_c)) /\ 
                        err_prop OS_ERR_DEL_NEXIST_IN_DOM vl' O O' ac
                    )
                    \/
                      (
                        exists t' st msg (* chm  *)sus,
                          get tls t' = Some (pr, st, msg, (* chm,  *)sus, d_c) (* same domain d_c as current task *) /\  
                            (
                              (((exists qid to, st = wait (os_stat_qpend qid) to) (* \/ *)
                                  (* (exists chid to, st = wait (os_stat_chpend chid) to) *)) /\
                                 err_prop OS_ERR_WAITING_ON_OBJ vl' O O' ac) 
                              \/
                                (st = rdy /\
                                   exists fts tids, 
                                     get O freetid = Some (freetidlist fts) /\
                                       get fts d_c = Some tids /\                                         
                                       exists tls', 
                                         joinsig t' (pr, st, msg, (* chm,  *)sus, d_c) tls' tls /\
                                           O' = set (set O abstcblsid (abstcblist tls'))
                                                  freetid (freetidlist (set fts d_c (tids ++ (t'::nil)))) /\
                                           ac = _TDelAct t' /\ vl' = cont :: nil)
                            )
                      )
                  )
      end
  | _ => err_prop MODEL_ERR_PARAMS (fst rst) O (snd rst) ac
  end. 

Definition taskdel (vl:vallist) : spec_code :=
  task_del_tcb_release (| vl |)
    ;;>
    (fun vl' =>
       match vl' with
         (Vint32 ierr) :: nil =>
           if Int.eq ierr Int.mone then
             sched trivial_asrt ;;
             spec_done (Vint32 (Int.repr OS_NO_ERROR) :: nil)
           else
             spec_done vl'
       | _ => spec_skip_step (| nil |)
       end). 

Definition taskdel_api := (taskdel, (Tint8, Tint8 :: nil)). 
