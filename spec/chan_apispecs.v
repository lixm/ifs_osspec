
Require Import Integers.
Require Import memory. 
Require Import language.
Require Import opsem.

Require Import state. 
Require Import specs_common. 

Definition empty: val := Vint32 (Int.mone).


(************************************* OSChanRecv *************************************)   

Definition chpend_prim (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match vl with
    Vint32 chid :: (* Vint32 vto :: *) nil =>
      ac = _TauAct /\ 
      match rst with
      | (vl', O') => 
          if negb (Int.lt chid Int.zero) then
            exists tls pr st m (* cm  *)sus d chs, 
              get O abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (pr, st, m, (* cm, *) sus, d) /\ 
                  get O chlsid = Some (chanlist chs) /\
                    let cid := Z.to_nat (Int.unsigned chid) in
                    match get chs cid with
                    | Some (d_src, d_dst, content) =>
                        if Int.eq d d_dst then
                          match content with
                          | SampleCh msg =>
                              vl' = msg :: nil /\ O' = O 
                          | QueueCh sz ms =>
                              match ms with
                              | msg :: ms' =>
                                  vl' = msg :: nil /\ 
                                    O' = set O chlsid (chanlist (set chs cid (d_src, d_dst, QueueCh sz ms'))) 
                              | nil =>
                                  vl' = empty :: nil /\ O' = O  
                              end
                          end
                        else
                          vl' = Vnull :: nil /\ O' = O 
                    | None =>
                        vl' = Vnull :: nil /\ O' = O 
                    end
          else
            vl' = Vnull :: nil /\ O' = O
      end
  | _ => fst rst = Vnull :: nil /\ snd rst = O /\ ac = _TauAct
  end. 

Definition chan_recv (vl:vallist) : spec_code := chpend_prim (| vl |).  

Definition chrecv_api := (chan_recv, (Tptr Tvoid, Tint8 :: (* Tint16 :: *) nil)).   


(************************************* OSChanSend *************************************)    

(* we do not perform re-scheduling even if there is a task made ready *)
(* this is because the readied task should belong to a different domain *) 
Definition chpost_prim (t: tid) (vl: vallist) (O : osabst) (ac: sem_act) (rst : vallist * osabst) :=
  match vl with
    Vint32 chid :: msg :: nil =>
      ac = _TauAct /\ 
      match rst with
      | (vl', O') => 
          if negb (Int.lt chid Int.zero) then
            match msg with
            | Vptr m =>
                let cid := Z.to_nat (Int.unsigned chid) in
                exists tls pr st m (* cm  *)sus d chs,  
                  get O abstcblsid = Some (abstcblist tls) /\
                    get tls t = Some (pr, st, m, (* cm,  *)sus, d) /\   
                      get O chlsid = Some (chanlist chs) /\ 
                        match get chs cid with 
                        | Some (d_src, d_dst, content) =>
                            if negb (Int.eq d_src d_dst) then 
                              if Int.eq d d_src then
                                match content with
                                | SampleCh v =>  
                                    O' = set O chlsid (chanlist (set chs cid (d_src, d_dst, SampleCh msg))) /\
                                      vl' = Vint32 (Int.repr OS_NO_ERROR) :: nil 
                                | QueueCh sz ms (* wls *) =>
                                    if Nat.ltb (length ms) sz then
                                      O' = set O chlsid (chanlist (set chs cid (d_src, d_dst, QueueCh sz (ms++(msg::nil))))) /\ 
                                        vl' = Vint32 (Int.repr OS_NO_ERROR) :: nil 
                                    else
                                      vl' = Vint32 (Int.repr OS_NO_ERROR) :: nil /\  O' = O 
                                end
                              else
                                vl' = Vint32 (Int.repr OS_ERR_WRONG_DOM) :: nil /\ O' = O
                            else
                              vl' = Vint32 (Int.repr OS_ERR_SAME_SRCDST) :: nil /\ O' = O
                        | _ => vl' = Vint32 (Int.repr OS_ERR_NO_CHAN) :: nil /\ O' = O
                        end                          
            | _ => vl' = Vint32 (Int.repr OS_ERR_INVALID_MSG) :: nil /\ O' = O
            end
          else
            vl' = Vint32 (Int.repr OS_ERR_INVALID_CHID) :: nil /\ O' = O
      end
  | _ => fst rst = Vint32 (Int.repr MODEL_ERR_PARAMS) :: nil /\ (snd rst) = O /\ ac = _TauAct
  end.

Definition chan_send (vl:vallist) : spec_code := chpost_prim (| vl |).  

Definition chsend_api := (chan_send, (Tint8, Tint8 :: Tptr Tvoid :: nil)).  
