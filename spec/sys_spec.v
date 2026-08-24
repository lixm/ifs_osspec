
Require Import memory.
Require Import language. 
Require Import state.
Require Import specs_common.
Require Import task_apispecs. 
Require Import mq_apispecs. 
Require Import chan_apispecs.
Require Import tick_spec.

Local Open Scope list_scope.


(* executable specs for the API functions *)

Definition api_spec_list :=
  (OSTaskCreate, taskcre_api) ::
    (OSTaskDel, taskdel_api) :: 
    (OSQPend, qpend_api) ::
    (OSQPost, qpost_api) ::
    (* (OSQCreate, qcre_api) :: *)
    (* (OSQDel, qdel_api) :: *)
    (OSChanRecv, chrecv_api) ::
    (OSChanSend, chsend_api) :: 
    nil.

Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.

Definition api_spec: osapispec := convert_api_spec api_spec_list.


(* executable spec for the interrupt handler *) 

Definition int_spec_list := (OSTickISR, tickisr) :: nil. 

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.

Definition int_spec: osintspec := convert_int_spec int_spec_list.

  
(* spec for the intra-domain scheduler *)

Definition get_hprio_in_dom (O:osabst) (td: task_dom) (t:tid) : Prop := 
  exists tls prio msg (* cm  *)sus,
    get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, rdy, msg, (* cm,  *)sus, td) /\ 
      forall t' prio' msg' (* cm'  *)sus',
        t' <> t ->
        get tls t' = Some (prio', rdy, msg', (* cm',  *)sus', td) ->
        Int.ltu prio prio' = true. 


(* system spec *)

Definition krnl_spec : osspec := (api_spec, int_spec, get_hprio_in_dom). 




  
