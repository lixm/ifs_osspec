
Require Import LibTactics.
Require Import memory.
Require Import opsem.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].


Ltac inv_hpstep_d := 
  match goal with H: context [hpstep_d] |- _ => inverts H end. 

Ltac inv_hpstep := 
  match goal with H: context [hpstep] |- _ => inverts H end. 

Ltac inv_htstep := 
  match goal with H: context [htstep] |- _ => inverts H end.

Ltac inv_htistep := 
  match goal with H: context [htistep] |- _ => inverts H end. 

Ltac inv_hapistep := 
  match goal with H: context [hapistep] |- _ => inverts H end.

Ltac inv_specstep := 
  match goal with H: context [spec_step] |- _ => inverts H end.

Ltac inv_tuple := 
  match goal with H: (_, _) = (_, _) |- _ => inverts H end.

Ltac inv_tuple_rev := 
  match goal with H: (_, _) = (_, _) |- _ => symmetry in H; inverts H end.


Ltac asst_same_code12 T t := 
  match goal with
  | HT1 : T t = Some ?C1,
      HT2 : T t = Some ?C2 |- _ => 
      let HC := fresh "HC" in
      assert (HC : C1 = C2) by
        (rewrite HT1 in HT2;
         inversion HT2;
         reflexivity)            
  end.          

Ltac asst_same_code21 T t := 
  match goal with
  | HT1 : T t = Some ?C1,
      HT2 : T t = Some ?C2 |- _ => 
      let HC := fresh "HC" in
      assert (HC : C1 = C2) by
        (rewrite HT2 in HT1;
         inversion HT1;
         reflexivity)            
  end.          

Ltac asst_same_code T1 T2 t HgTeq := 
  match goal with
  | HT1 : T1 t = Some ?C1,
      HT2 : T2 t = Some ?C2 |- _ => 
      let HC := fresh "HC" in
      assert (HC : C1 = C2) by
        (rewrite HT1, HT2 in HgTeq;
         inversion HgTeq;
         reflexivity)            
  end.          

Ltac asst_same_ust ust1 ust2 td Husteq := 
  match goal with
  | HU1 : get ust1 td = Some ?sst1,
      HU2 : get ust2 td = Some ?sst2 |- _ => 
      let HU := fresh "HU" in
      assert (HU : sst1 = sst2) by
        (rewrite HU1, HU2 in Husteq;
         inversion Husteq; 
         reflexivity)            
  end.          


Ltac rn_or Hname :=
  match goal with H: _ \/ _ |- _ => rename H into Hname end.


Ltac inv_hctr H :=
  match goal with
    H': context[H] |- _ => inverts H'
  end.


Ltac d_if_hyp :=
  let E := fresh "E" in 
  match goal with
    H: context[if ?t then _ else _] |- _ => destruct t eqn: E
  end.

Ltac d_mt_hyp :=
  let E := fresh "E" in 
  match goal with
  | H: context [match ?t with _ => _ end] |- _ => 
      destruct t eqn:E
  end.


(**) 

Ltac des_pre2 H :=
  let Hdte := fresh "Hdte" in
  let td' := fresh "td'" in 
  destruct H as (Hpre11 & Hpre12 & Hdte & td' & Hsd1 & Hsd2 & Hflt & Hdte').


(**)

Ltac uni_12 t :=
  match goal with
  | H1 : t = ?x, H2 : t = ?y |- _ =>
      rewrite H1 in H2; inverts H2
  end.

Ltac uni_21 t :=
  match goal with
  | H1 : t = ?x, H2 : t = ?y |- _ =>
      rewrite H2 in H1; inverts H1
  end.

Ltac uni_12_sym t :=
  match goal with
  | H1 : t = ?x, H2 : t = ?y |- _ =>
      rewrite H1 in H2; symmetry in H2; inverts H2
  end.
  
Ltac uni_21_sym t :=
  match goal with
  | H1 : t = ?x, H2 : t = ?y |- _ =>
      rewrite H2 in H1; symmetry in H1; inverts H1
  end.


(**)

Ltac rew_neq :=
  let Hf := fresh "Hf" in 
  rewrite neq_set_get; eauto; try (introv Hf; inverts Hf).

Ltac rew_neq_in H :=
  let Hf := fresh "Hf" in 
  rewrite neq_set_get in H; eauto; try (introv Hf; inverts Hf).

(**)

