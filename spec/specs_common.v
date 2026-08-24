
Require Import memory.
Require Import language. 

Require Import state. 

Definition NO_ERR := 0%Z. 

Definition MODEL_ERR_PARAMS := 1%Z.
Definition MODEL_ERR_NO_TLS := 2%Z.  
Definition MODEL_ERR_NO_ELS := 3%Z.
(* Definition MODEL_ERR_NO_TASK := 4%Z.   *)
Definition MODEL_ERR_NO_FREETIDMP :=5%Z.  
Definition MODEL_ERR_NO_PTLS := 6%Z. 
Definition MODEL_ERR_NO_UFLIST := 7%Z.
Definition MODEL_ERR_NO_CHLS := 8%Z.
Definition MODEL_ERR_NO_TM := 8%Z.
Definition MODEL_ERR_NO_DOMT := 9%Z. 
Definition MODEL_ERROR_NO_SCHIDX := 10%Z. 
Definition MODEL_ERROR_NO_SCHLEN := 11%Z. 
Definition MODEL_ERROR_NO_CDOM := 12%Z. 
Definition MODEL_ERROR_NO_LDOM := 13%Z.  
Definition MODEL_ERROR_NO_DSCH := 14%Z.  
Definition MODEL_ERR_NO_FREETIDLS := 15%Z.
Definition MODEL_ERR_NO_FREEQIDMP :=16%Z.   
Definition MODEL_ERR_NO_FREEQIDLS := 17%Z.
Definition MODEL_ERR_NO_TCST := 18%Z. 

Definition OS_NO_ERROR := 0%Z.  
Definition OS_ERR_POST_NULL_PTR := 51%Z. 
Definition MSGQ_OVF_ERR := 52%Z. 
Definition OS_ERR_IDLE_PRIO := 53%Z.  
Definition OS_ERR_PEVENT_NULL := 54%Z.
Definition OS_ERR_NO_QUE := 55%Z. 
Definition OS_ERR_TIMEOUT := 56%Z.  
Definition OS_ERR_NO_TASK := 57%Z.

Definition OS_ERR_PRIO_INVALID := 61%Z.   
Definition OS_ERR_NO_MORE_TCB := 62%Z.   
Definition OS_ERR_NO_UFUNC := 63%Z. 
Definition OS_ERR_DEL_IDLE := 64%Z. 
Definition OS_ERR_DEL_NEXIST_IN_DOM := 65%Z.
Definition OS_ERR_PRIO_EXIST_IN_DOM := 66%Z. 

Definition OS_ERR_NO_CHAN := 67%Z.
Definition OS_ERR_EMPTY_CHAN := 68%Z. 
Definition OS_ERR_INVALID_CHID := 69%Z. 

Definition OS_ERR_INVALID_QSIZE := 71%Z. 
Definition CHAN_OVF_ERR := 72%Z. 
Definition OS_ERR_SAME_SRCDST := 73%Z. 

Definition OS_ERR_NO_MORE_QID := 74%Z.

Definition OS_ERR_TASKS_WAITING := 75%Z.

Definition OS_ERR_IN_QOP := 76%Z. 
Definition OS_ERR_WAITING_ON_OBJ := 77%Z. 

Definition OS_ERR_WRONG_DOM := 81%Z. 
Definition OS_ERR_NO_DSCH_CELL := 82%Z. 

(* Definition OS_ERR_DEL_MQ_IN_OP := 83%Z. *)
Definition OS_ERR_NO_QUE_IN_DOM := 84%Z.
Definition OS_ERR_INVALID_MSG := 85%Z. 

Definition OS_IDLE_PRIO := 63%Z.

Definition OS_LOWEST_PRIO := OS_IDLE_PRIO.

Definition qpend_id := 101%Z.
Definition qpost_id := 102%Z.
Definition chan_recv_id := 105%Z.
Definition chan_send_id := 106%Z.

(***************************** function IDs *****************************)

Definition OSQPend := 1001%Z.
Definition OSQPost := 1002%Z.
Definition OSQCreate := 1003%Z.
Definition OSQDel := 1004%Z.

Definition OSTaskCreate := 1011%Z.
Definition OSTaskDel := 1012%Z.

Definition OSChanSend := 1021%Z.
Definition OSChanRecv := 1022%Z.

Definition OSTickISR := 0%nat. 

(***********************************************************************)

Definition err_prop (err: Z) (vl: vallist) (O O': osabst) (ac: sem_act) :=
  vl = Vint32 (Int.repr err) :: nil /\ O' = O /\ ac = _TauAct. 

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.

(* the definition works if all tasks in wl are in the domain d *)
(* the system just obtains the ID of the highest prio waiting task
   --- it does not care about whether the highest prio waiting task is suspended *)   
Definition GetHWait (tls: TcbMod.map) (wl: list tid) (t: tid) := 
  In t wl /\ 
    exists p st msg (* chm  *)sus d,
      get tls t = Some (p,st,msg,(* chm, *)sus,d) /\
        forall t',
          t <> t' -> 
          In t' wl -> 
          exists p' st' msg' (* chm'  *)sus' d',
            get tls t' = Some (p',st',msg',(* chm', *)sus',d') /\ (Int.ltu p p' = true)%Z.   
    
        

