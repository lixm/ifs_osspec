
Require Import memory. 
Require Import language.
Require Import opsem.
Require Import rules.
Require Import state.

Definition rly_tsk_env (t: tid) (O O': osabst): Prop :=
  (forall td, sdom_ O t td -> sdom_ O' t td) /\
    (forall q td, q_sdom_ O q td -> q_sdom_ O' q td).

Definition guar_tsk_env (t: tid) (O O': osabst): Prop :=
  (forall t' td, t <> t' -> sdom_ O t' td -> sdom_ O' t' td) /\
    (forall q td, q_sdom_ O q td -> q_sdom_ O' q td).

Definition rly_itp_env (t: tid) (O O': osabst): Prop :=
  True.

Definition guar_itp_env (t: tid) (O O': osabst): Prop :=
  (forall t' td, sdom_ O t' td -> sdom_ O' t' td) /\
    (forall q td, q_sdom_ O q td -> q_sdom_ O' q td).


