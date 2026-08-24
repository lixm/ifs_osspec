
Require Import memory.
Require Import language.
Require Import opsem.
Require Import rules. 
Require Import state.


Inductive flows_to : flows_to_t :=

| flt_refl: forall d, flows_to d d 

| flt_sch_to_all: forall d, flows_to SchedDom d

| flt_chs:
  forall c sd dd ctp, 
    get chcfg c = Some (sd, dd, ctp) ->
    flows_to (TaskDom sd) (TaskDom dd). 

