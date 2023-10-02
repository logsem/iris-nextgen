From stdpp Require Export coPset.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import wsat later_credits invariants.
From iris.prelude Require Import options.

From nextgen Require Import nextgen_pointwise gmap_view_transformation.
  
(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [wsatGS] module. The module [wsatGS] is thus exported in
[fancy_updates], where [wsat] is only imported. *)
Module wsatGS.

Class pick_transform_rel (A : cmra) : Type := TransRel {
  C : Type;
  CR : relation C;
  C_pre :> Transitive CR;
  C_pick : C -> (A -> A);
  C_pick_cmramorphism :> ∀ (c : C), CmraMorphism (C_pick c);
  C_dec :> ∀ (c1 c2 : C), Decision (CR c1 c2)
}.
  
Class wsatGIndpreS (Σ : gFunctors) (Ω : gTransformations Σ) (A : cmra) (pick: pick_transform_rel A) : Set := WsatGIndpreS {
  wsatGpreS_inv : genIndInG Σ Ω (gmap_viewR positive (laterO (iPropO Σ)));
  wsatGpreS_func : noTwoTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) A;
  wsatGpreS_enabled : genIndInG Σ Ω coPset_disjR;
  wsatGpreS_disabled : genIndInG Σ Ω (gset_disjR positive);
}.

Class wsatGIndS (Σ : gFunctors) (Ω : gTransformations Σ) (A : cmra) (pick: pick_transform_rel A) : Set := WsatGInd {
  wsat_inG : wsatGIndpreS Σ Ω A pick;
  invariant_name : gname;
  enabled_name : gname;
  disabled_name : gname;
  pick_name : gname;                                                                               
}.
Global Hint Mode wsatGIndpreS - - - - : typeclass_instances.
Global Hint Mode wsatGIndS - - - - : typeclass_instances.


Class lcGIndpreS (Σ : gFunctors) (Ω : gTransformations Σ) := LcGIndpreS {
  lcGpreS_inG : genIndInG Σ Ω (authR natUR)
}.

Class lcGIndS (Σ : gFunctors) (Ω : gTransformations Σ) := LcGIndS {
  lcGS_inG : genIndInG Σ Ω (authR natUR);
  lcGS_name : gname;
}.
Global Hint Mode lcGIndpreS - - : typeclass_instances.
Global Hint Mode lcGIndS - - : typeclass_instances.

End wsatGS.
Import wsatGS.
Local Existing Instances wsat_inG wsatGpreS_inv wsatGpreS_enabled wsatGpreS_disabled.


#[global] Instance into_wsatpres `{pick: pick_transform_rel A} `{!wsatGIndpreS Σ Ω A pick} : wsatGpreS Σ :=
  WsatGpreS Σ wsatGpreS_inv.(genInG_inG) wsatGpreS_enabled.(genInG_inG) wsatGpreS_disabled.(genInG_inG).
  
#[global] Instance into_wsats `{pick: pick_transform_rel A} `{!wsatGIndS Σ Ω A pick} : wsatGS Σ  :=
  WsatG Σ (@into_wsatpres A pick Σ Ω wsat_inG) invariant_name enabled_name disabled_name.

#[global] Instance into_lcpres `{Hlc: lcGIndpreS Σ Ω} : lcGpreS Σ :=
  LcGpreS Σ lcGpreS_inG.(genInG_inG).

#[global] Instance into_lcs `{Hlc: lcGIndS Σ Ω} : lcGS Σ :=
  LcGS Σ lcGS_inG.(genInG_inG) lcGS_name.

#[global] Instance cmra_morphism_pick `{Hpre : pick_transform_rel A} : ∀ c', CmraMorphism (C_pick c') :=
  Hpre.(C_pick_cmramorphism).

#[global] Instance wsat_notrans_inl `{wsat: !wsatGIndS Σ Ω A pick} : noTransInG Σ Ω A | 2 :=
  (wsatGpreS_func.(noTransInG_B_inG)).

#[global] Instance wsat_notrans_inr `{wsat: !wsatGIndS Σ Ω A pick} : noTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) | 2 :=
  (wsatGpreS_func.(noTransInG_A_inG)).

#[local] Instance inG_wsatGS_inl `{Hpre : wsatGIndpreS Σ Ω T} : inG Σ (gmap_viewR positive (optionO (leibnizO C))) :=
  (wsatGpreS_func.(noTransInG_A_inG)).(noTransInG_inG).

#[local] Instance inG_wsatGS_inr `{Hpre : wsatGIndpreS Σ Ω T} : inG Σ T :=
  (wsatGpreS_func.(noTransInG_B_inG)).(noTransInG_inG).

Definition pick_coerce `{pick_transform_rel A} (c : option C) : optionO (leibnizO C) := c.

Definition ownC `{pick: pick_transform_rel A} `{!wsatGIndS Σ Ω A pick} (i : positive) (c : C) : iProp Σ :=
  own pick_name (gmap_view_frag i DfracDiscarded (pick_coerce (Some c))).
Global Typeclasses Opaque ownC.
Global Instance: Params (@ownC) 2 := {}.

Definition ownN `{pick: pick_transform_rel A} `{!wsatGIndS Σ Ω A pick} (i : positive) : iProp Σ :=
  own pick_name (gmap_view_frag i DfracDiscarded None).
Global Typeclasses Opaque ownN.
Global Instance: Params (@ownN) 1 := {}.

#[global] Instance ownC_persistent `{pick: pick_transform_rel A} `{!wsatGIndS Σ Ω A pick} (i : positive) (c : C) : Persistent (ownC i c).
Proof. rewrite /ownC. apply _. Qed.
#[global] Instance ownN_persistent `{pick: pick_transform_rel A} `{!wsatGIndS Σ Ω A pick} (i : positive) : Persistent (ownN i).
Proof. rewrite /ownN. apply _. Qed.


Definition inv_pick_cut `{pick_transform_rel A} (c : C) (i : positive) (v : optionO (leibnizO C)) :=
 Some (v ≫= (λ c', if decide (CR c' c) then Some c' else None)).
Definition inv_pick_transform `{pick_transform_rel A} (c : C) := (map_entry_lift_gmap_view (inv_pick_cut c)).

#[global] Instance inv_pick_mapTrans `{pick_transform_rel A} (c : C) : MapTrans (inv_pick_cut c).
Proof.
  split.
  - intros l v1 Hcontr. done.
  - intros k n v1 v2 Hv1. rewrite /inv_pick_cut /=.
    constructor. destruct v1,v2;inversion Hv1;simplify_eq =>/= //.
    rewrite H2. auto.    
Qed.

#[global] Instance cmra_morphism_pick_transform `{pick_transform_rel A} : ∀ c', CmraMorphism (inv_pick_transform c') :=
  λ c', gMapTrans_lift_CmraMorphism (inv_pick_cut c').

Definition inv_cond {Σ Ω A} `{pick: pick_transform_rel A} {wsat: wsatGIndS Σ Ω A pick} Q (c : C) : iProp Σ :=
  ■ (∀ (c' : C), ⌜CR c c'⌝ -∗ Q -∗ ⚡={transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω}=> Q).

Definition wsat `{pick: pick_transform_rel A} `{!wsatGIndS Σ Ω A pick} : iProp Σ :=
  locked (∃ (I : gmap positive (iProp Σ)) (F : gmap positive (option C)),
    ⌜dom I = dom F⌝ ∗
     own invariant_name (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
     own pick_name (gmap_view_auth (DfracOwn 1) (pick_coerce <$> F)) ∗
    [∗ map] i ↦ Q ∈ I, (ownN i ∨ ∃ (c : C), ownC i c ∗ inv_cond Q c ∗ (▷ Q ∗ ownD {[i]} ∨ ownE {[i]})))%I.

Section wsat.
Context `{!wsatGIndS Σ Ω A pick}.
Implicit Types P : iProp Σ.

Lemma ownCN i c : (ownC i c ∗ ownN i) ⊢ False.
Proof.
  rewrite /ownC /ownN.
  rewrite -own_op own_valid gmap_view_frag_op_validI option_equivI.
  rewrite /pick_coerce. iIntros "[? ?]". done.
Qed.

Lemma ownC_eq i c c' : (ownC i c ∗ ownC i c') ⊢ (⌜c = c'⌝).
Proof.
  rewrite /ownC /ownN.
  rewrite -own_op own_valid gmap_view_frag_op_validI option_equivI.
  rewrite /pick_coerce. iIntros "[? %]". iPureIntro. auto.
Qed.

Lemma ownI_open i c P : wsat ∗ ownI i P ∗ ownC i c ∗ ownE {[i]} ⊢ wsat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & Hc & HiE)". iDestruct "Hw" as (I F Hdom) "[Hw [HF HI]]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[Hnone|Hsome] HI]"; eauto.
  - by iDestruct (ownCN with "[$]") as "?".
  - iDestruct "Hsome" as (c') "[#Hc' [#Hcond [[HQ HD] | HiE']]]".
    + iFrame. iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
      iExists I,F. iFrame "Hw HF". iSplit;auto. iApply (big_sepM_delete _ _ i); eauto.
      iFrame "HI". iRight. eauto.
    + iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma ownI_close i c P : wsat ∗ ownI i P ∗ ownC i c ∗ ▷ P ∗ ownD {[i]} ⊢ wsat ∗ ownE {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & Hc & HP & HiD)". iDestruct "Hw" as (I F Hdom) "[Hw [HF HI]]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[Hnone|Hsome] HI]"; eauto.
  - by iDestruct (ownCN with "[$]") as "?".
  - iDestruct "Hsome" as (c') "[#Hc' [#Hcond [[HQ HD] | HiE']]]".
    + iDestruct (ownD_singleton_twice with "[$]") as %[].
    + iFrame. iExists I, F. iFrame "Hw HF". iSplit;auto. iApply (big_sepM_delete _ _ i); eauto.
      iFrame "HI #". iRight. iExists _.
      iDestruct (ownC_eq with "[$]") as %Heq. subst c'.
      iFrame "Hc' Hcond". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma ownI_alloc φ P c :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  inv_cond P c ∗
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P ∗ ownC i c.
Proof.
  iIntros (Hfresh) "[#Hcond [Hw HP]]". rewrite /wsat -!lock.
  iDestruct "Hw" as (I F Hdom) "[Hw [HF HI]]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iMod (own_update with "HF") as "[HF HiC]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    rewrite /= lookup_fmap. assert (F !! i = None) as -> =>//.
    apply not_elem_of_dom. rewrite -Hdom.
    apply not_elem_of_dom =>//. }
  iModIntro; iExists i;  iSplit; [done|].
  rewrite /ownI; iFrame "HiP".
  rewrite /ownC. iDestruct "HiC" as "#HiC". iFrame "HiC".
  iExists (<[i:=P]>I),(<[i:=Some c]>F). iSplit.
  { iPureIntro. set_solver. }
  iSplitL "Hw".
  { by rewrite fmap_insert. }
  iSplitL "HF".
  { by rewrite fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI #". iRight. iExists c. rewrite /ownC. iFrame "HiC Hcond".
  iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_open φ P c :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  inv_cond P c ∗ wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ wsat) ∗ ownI i P ∗ ownC i c ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "[#Hcond Hw]". rewrite /wsat -!lock. iDestruct "Hw" as (I F Hdom) "[Hw [HF HI]]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iMod (own_update with "HF") as "[HF HiC]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    rewrite /= lookup_fmap. assert (F !! i = None) as -> =>//.
    apply not_elem_of_dom. rewrite -Hdom.
    apply not_elem_of_dom =>//. }
  iModIntro; iExists i;  iSplit; [done|].
  rewrite /ownI; iFrame "HiP".
  iDestruct "HiC" as "#HiC".
  rewrite /ownC; iFrame "HiC".
  unfold ownD. simpl. iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I),(<[i:=Some c]>F); iSplit.
  { iPureIntro. set_solver. }
  iSplitL "Hw".  
  { by rewrite fmap_insert. }
  iSplitL "HF".  
  { by rewrite fmap_insert. }  
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI #". iRight. iExists _. rewrite /ownC. iFrame "HiC Hcond". by iRight.
Qed.
End wsat.

(* Allocation of an initial world *)
Lemma wsat_alloc `{!wsatGIndpreS Σ Ω A pick} : ⊢ |==> ∃ _ : wsatGIndS Σ Ω A pick, wsat ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (own_alloc (@gmap_view_auth _ _ _ (laterO (iPropO Σ)) (DfracOwn 1) ∅)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (@gmap_view_auth _ _ _ (optionO (leibnizO C)) (DfracOwn 1) ∅)) as (γI') "HI'";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro. iExists (WsatGInd _ _ _ _ _ γI γE γD γI').
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅,∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.

Lemma lc_ind_insert_intro `{lcGIndS Σ Ω} `{noTransInG Σ Ω A} (m : nat) (t : A → A) `{!CmraMorphism t} :
  £ m ⊢ ⚡={transmap_insert_inG t Ω}=> £ m.
Proof.
  iIntros "Hm".
  unfold lc. rewrite seal_eq /= /later_credits.lc_def /=.
  iModIntro. iFrame.
Qed.

Lemma lc_ind_insert_two_intro `{lcGIndS Σ Ω} `{noTwoTransInG Σ Ω A D} (m : nat)
  (t : A → A) (f : D -> D) `{!CmraMorphism t} `{!CmraMorphism f} :
  £ m ⊢ ⚡={transmap_insert_two_inG t f Ω}=> £ m.
Proof.
  iIntros "Hm".
  unfold lc. rewrite seal_eq /= /later_credits.lc_def /=.
  iDestruct (transmap_own_insert_two_other t f with "Hm") as "Hm".
  iModIntro. iFrame.
Qed.

Lemma lc_ind_intro `{lcGIndS Σ Ω} (m : nat) :
  £ m ⊢ ⚡={Ω}=> £ m.
Proof.
  iIntros "Hm".
  unfold lc. rewrite seal_eq /= /later_credits.lc_def /=.
  iModIntro. iFrame.
Qed.

Lemma ls_ind_intro `{lcGIndS Σ Ω} (m : nat) :
  later_credits.lc_supply m ⊢ ⚡={Ω}=> later_credits.lc_supply m.
Proof.
  iIntros "Hm".
  unfold later_credits.lc_supply. rewrite seal_eq /= /later_credits.lc_supply_def.
  iModIntro. iFrame.
Qed.

Lemma ls_ind_insert_intro `{lcGIndS Σ Ω} `{noTransInG Σ Ω A} (t : A → A) `{!CmraMorphism t} (m : nat) :
  later_credits.lc_supply m ⊢ ⚡={transmap_insert_inG t Ω}=> later_credits.lc_supply m.
Proof.
  iIntros "Hm".
  unfold later_credits.lc_supply. rewrite seal_eq /= /later_credits.lc_supply_def.
  iModIntro. iFrame.
Qed.

Lemma ls_ind_insert_two_intro `{lcGIndS Σ Ω} `{noTwoTransInG Σ Ω A B}
  (t : A → A) (f : B → B) `{!CmraMorphism t} `{!CmraMorphism f} (m : nat) :
  later_credits.lc_supply m ⊢ ⚡={transmap_insert_two_inG t f Ω}=> later_credits.lc_supply m.
Proof.
  iIntros "Hm".
  unfold later_credits.lc_supply. rewrite seal_eq /= /later_credits.lc_supply_def.
  iDestruct (transmap_own_insert_two_other t f with "Hm") as "Hm".
  iModIntro. iFrame.
Qed.



Lemma ownE_ind_insert_intro `{!wsatGIndS Σ Ω A pick} `{noTransInG Σ Ω B} (E: coPset) (t : B → B) `{!CmraMorphism t} :
  ownE E ⊢ ⚡={transmap_insert_inG t Ω}=> ownE E.
Proof.
  iIntros "Hwsat". rewrite /ownE.
  iModIntro. iFrame.
Qed.

Lemma ownE_ind_insert_two_intro `{!wsatGIndS Σ Ω A pick} `{noTwoTransInG Σ Ω B D}
  (E: coPset) (t : B → B) (f : D -> D) `{!CmraMorphism t} `{!CmraMorphism f} :
  ownE E ⊢ ⚡={transmap_insert_two_inG t f Ω}=> ownE E.
Proof.
  iIntros "Hwsat". rewrite /ownE.
  iDestruct (transmap_own_insert_two_other t f with "Hwsat") as "Hwsat".
  iModIntro. iFrame.
Qed.

Lemma ownE_ind_intro `{!wsatGIndS Σ Ω A pick} (E: coPset) :
  ownE E ⊢ ⚡={Ω}=> ownE E.
Proof.
  iIntros "Hwsat".
  unfold ownE.
  iModIntro. iFrame.
Qed.

Lemma ownD_ind_insert_intro `{!wsatGIndS Σ Ω A pick} `{noTransInG Σ Ω B} (E: gset positive) (t : B → B) `{!CmraMorphism t} :
  ownD E ⊢ ⚡={transmap_insert_inG t Ω}=> ownD E.
Proof.
  iIntros "Hwsat".
  unfold ownD.
  iModIntro. iFrame.
Qed.

Lemma ownD_ind_insert_two_intro `{!wsatGIndS Σ Ω A pick} `{noTwoTransInG Σ Ω B D}
  (E: gset positive) (t : B → B) (f : D -> D) `{!CmraMorphism t} `{!CmraMorphism f} :
  ownD E ⊢ ⚡={transmap_insert_two_inG t f Ω}=> ownD E.
Proof.
  iIntros "Hwsat".
  unfold ownD.
  iDestruct (transmap_own_insert_two_other t f with "Hwsat") as "Hwsat".
  iModIntro. iFrame.
Qed.


(* Lemma ownD_ind_insert_intro `{!wsatGIndS Σ Ω A pick} (E: gset positive) (c : C) :  *)
(*   ownD E ⊢ ⚡={transmap_insert_inG (C_pick c) Ω}=> ownD E. *)
(* Proof. *)
(*   iIntros "Hwsat". *)
(*   destruct wsatGIndS0,wsat_inG0. *)
(*   assert (noTransInG Σ Ω A);[apply _|]. *)
(*   iApply (@ownD_ind_insert_intro' _ _ A _ _ A). *)
(*   iFrame. *)
(* Qed. *)

(* Lemma ownD_ind_pick_map_intro `{!wsatGIndS Σ Ω A pick} (E: gset positive) (c : C) : *)
(*   ownD E ⊢ ⚡={transmap_insert_inG (inv_pick_transform c) Ω}=> ownD E. *)
(* Proof. *)
(*   iIntros "Hwsat". *)
(*   destruct wsatGIndS0,wsat_inG0. *)
(*   assert (noTransInG Σ Ω A);[apply _|]. *)
(*   iApply ownD_ind_insert_intro'. *)
(*   iFrame. *)
(* Qed. *)

Lemma ownD_ind_intro `{wsatGIndS Σ Ω} (E: gset positive) :
  ownD E ⊢ ⚡={Ω}=> ownD E.
Proof.
  iIntros "Hwsat".
  unfold ownD.
  iModIntro. iFrame.
Qed.



Lemma auth_invariant_insert_intro `{!wsatGIndS Σ Ω A pick} `{i : noTransInG Σ Ω B}
  (I : gmap positive (laterO (iPropO Σ))) (t : B → B) `{!CmraMorphism t} :
  own invariant_name (gmap_view_auth (DfracOwn 1) I)
    ⊢ ⚡={transmap_insert_inG t Ω}=> own invariant_name (gmap_view_auth (DfracOwn 1) I).
Proof.
  iIntros "Hi".
  iModIntro.
  iFrame.
Qed.

Lemma auth_invariant_insert_two_intro `{!wsatGIndS Σ Ω A pick} `{i : noTwoTransInG Σ Ω B D}
  (I : gmap positive (laterO (iPropO Σ))) (t : B → B) (f : D -> D) `{!CmraMorphism t} `{!CmraMorphism f} :
  own invariant_name (gmap_view_auth (DfracOwn 1) I)
    ⊢ ⚡={transmap_insert_two_inG t f Ω}=> own invariant_name (gmap_view_auth (DfracOwn 1) I).
Proof.
  iIntros "Hi".
  iDestruct (transmap_own_insert_two_other t f with "Hi") as "Ho".
  iModIntro.
  iFrame.
Qed.

Lemma frag_invariant_insert_intro `{!wsatGIndS Σ Ω A pick} `{i : noTransInG Σ Ω B} (t : B → B)
  (j : positive) (P : iProp Σ) `{!CmraMorphism t} :
  ownI j P
    ⊢ ⚡={transmap_insert_inG t Ω}=> ownI j P.
Proof.
  rewrite /ownI /=.
  iIntros "Hi".
  iModIntro.
  iFrame.
Qed.

Lemma frag_invariant_insert_two_intro `{!wsatGIndS Σ Ω A pick} `{i : noTwoTransInG Σ Ω B D}
  (j : positive) (P : iProp Σ)
  (t : B → B) (f : D → D) `{!CmraMorphism t} `{!CmraMorphism f} :
  ownI j P
    ⊢ ⚡={transmap_insert_two_inG t f Ω}=> ownI j P.
Proof.
  rewrite /ownI /=.
  iIntros "Hi".
  iDestruct (transmap_own_insert_two_other t f with "Hi") as "Ho".
  iModIntro.
  iFrame.
Qed.

Lemma auth_pick_map_insert_intro `{!wsatGIndS Σ Ω A pick} F (t : A → A) `{!CmraMorphism t}  :
  own pick_name (gmap_view_auth (DfracOwn 1) F) ⊢
    ⚡={transmap_insert_inG t Ω}=> own pick_name (gmap_view_auth (DfracOwn 1) F).
Proof.
  iIntros "Hc".
  iApply transmap_own_insert_other_left. iFrame.
Qed.

Lemma auth_pick_map_transform_intro `{!wsatGIndS Σ Ω A pick} F (c : C) :
  own pick_name (gmap_view_auth (DfracOwn 1) F) ⊢
    ⚡={transmap_insert_inG (inv_pick_transform c) Ω}=> own pick_name (gmap_view_auth (DfracOwn 1) (map_imap (inv_pick_cut c) F)).
Proof.
  iIntros "Hc". rewrite -map_entry_lift_gmap_view_auth.
  iApply transmap_own_insert. iFrame.
Qed.

Lemma auth_pick_map_transform_two_intro `{!wsatGIndS Σ Ω A pick} F (c : C) :
  own pick_name (gmap_view_auth (DfracOwn 1) F) ⊢
    ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=> own pick_name (gmap_view_auth (DfracOwn 1) (map_imap (inv_pick_cut c) F)).
Proof.
  iIntros "Hc". rewrite -map_entry_lift_gmap_view_auth.
  iApply transmap_own_insert_two_left. iFrame.
Qed.

Lemma frag_pick_map_insert_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c : C) (t : A → A) `{!CmraMorphism t} :
  ownC i c ⊢
    ⚡={transmap_insert_inG t Ω}=> ownC i c.
Proof.
  iIntros "Hc". rewrite /ownC.
  iApply transmap_own_insert_other_left. iFrame.
Qed.

Lemma frag_pick_map_transform_Some_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c c' : C) :
  CR c' c ->
  ownC i c' ⊢
    ⚡={transmap_insert_inG (inv_pick_transform c) Ω}=> ownC i c'.
Proof.
  iIntros (HCR) "Hc". rewrite /ownC.
  iDestruct (@transmap_own_insert _ Σ Ω (@wsat_notrans_inr _ _ _ _ wsatGIndS0)
               (inv_pick_transform c) with "Hc") as "Hc".
  rewrite {2}/inv_pick_transform.
  unfold map_entry_lift_gmap_view, cmra_morphism_extra.fmap_view, cmra_morphism_extra.fmap_pair. simpl.
  rewrite /gMapTrans_frag_lift. rewrite -insert_empty.
  erewrite map_imap_insert_Some;
    [|rewrite /map_trans_frag_lift agree_option_map_to_agree /= //].
  rewrite decide_True//.
Qed.

Lemma frag_pick_map_transform_None_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c c' : C) :
  ¬ CR c' c ->
  ownC i c' ⊢
    ⚡={transmap_insert_inG (inv_pick_transform c) Ω}=> ownN i.
Proof.
  iIntros (HCR) "Hc". rewrite /ownC.
  iDestruct (@transmap_own_insert _ Σ Ω (@wsat_notrans_inr _ _ _ _ wsatGIndS0)
               (inv_pick_transform c) with "Hc") as "Hc".
  rewrite {2}/inv_pick_transform.
  unfold map_entry_lift_gmap_view, cmra_morphism_extra.fmap_view, cmra_morphism_extra.fmap_pair. simpl.
  rewrite /gMapTrans_frag_lift. rewrite -insert_empty.
  erewrite map_imap_insert_Some;
    [|rewrite /map_trans_frag_lift agree_option_map_to_agree /= //].
  rewrite decide_False//.
Qed.

Lemma frag_pick_map_transform_two_Some_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c c' : C) :
  CR c' c ->
  ownC i c' ⊢
    ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=> ownC i c'.
Proof.
  iIntros (HCR) "Hc". rewrite /ownC.
  iDestruct (@transmap_own_insert_two_left _ _ Σ Ω ((wsatGIndS0.(wsat_inG)).(wsatGpreS_func))
               (inv_pick_transform c) (C_pick c) with "Hc") as "Hc".
  iModIntro.
  rewrite {1}/inv_pick_transform.
  unfold map_entry_lift_gmap_view, cmra_morphism_extra.fmap_view, cmra_morphism_extra.fmap_pair. simpl.
  rewrite /gMapTrans_frag_lift. rewrite -insert_empty.
  erewrite map_imap_insert_Some;
    [|rewrite /map_trans_frag_lift agree_option_map_to_agree /= //].
  rewrite decide_True//.
Qed.

Lemma frag_pick_map_transform_two_None_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c c' : C) :
  ¬ CR c' c ->
  ownC i c' ⊢
    ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=> ownN i.
Proof.
  iIntros (HCR) "Hc". rewrite /ownC.
  iDestruct (@transmap_own_insert_two_left _ _ Σ Ω ((wsatGIndS0.(wsat_inG)).(wsatGpreS_func))
               (inv_pick_transform c) (C_pick c) with "Hc") as "Hc".
  rewrite {2}/inv_pick_transform.
  unfold map_entry_lift_gmap_view, cmra_morphism_extra.fmap_view, cmra_morphism_extra.fmap_pair. simpl.
  rewrite /gMapTrans_frag_lift. rewrite -insert_empty.
  erewrite map_imap_insert_Some;
    [|rewrite /map_trans_frag_lift agree_option_map_to_agree /= //].
  rewrite decide_False//.
Qed.

Lemma frag_pick_map_None_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c : C) :
  ownN i ⊢
    ⚡={transmap_insert_inG (inv_pick_transform c) Ω}=> ownN i.
Proof.
  iIntros "Hc". rewrite /ownN.
  iDestruct (@transmap_own_insert _ Σ Ω (@wsat_notrans_inr _ _ _ _ wsatGIndS0)
               (inv_pick_transform c) with "Hc") as "Hc".
  rewrite {2}/inv_pick_transform.
  unfold map_entry_lift_gmap_view, cmra_morphism_extra.fmap_view, cmra_morphism_extra.fmap_pair. simpl.
  rewrite /gMapTrans_frag_lift. rewrite -insert_empty.
  erewrite map_imap_insert_Some;
    [|rewrite /map_trans_frag_lift agree_option_map_to_agree /= //].
  auto.
Qed.

Lemma frag_pick_map_None_two_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (c : C) :
  ownN i ⊢
    ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=> ownN i.
Proof.
  iIntros "Hc". rewrite /ownN.
  iDestruct (@transmap_own_insert_two_left _ _ Σ Ω ((wsatGIndS0.(wsat_inG)).(wsatGpreS_func))
               (inv_pick_transform c) (C_pick c) with "Hc") as "Hc".
  rewrite {2}/inv_pick_transform.
  unfold map_entry_lift_gmap_view, cmra_morphism_extra.fmap_view, cmra_morphism_extra.fmap_pair. simpl.
  rewrite /gMapTrans_frag_lift. rewrite -insert_empty.
  erewrite map_imap_insert_Some;
    [|rewrite /map_trans_frag_lift agree_option_map_to_agree /= //].
  auto.
Qed.

Lemma ownN_insert_intro `{!wsatGIndS Σ Ω A pick} (i : positive) (t : A → A) `{!CmraMorphism t} :
  ownN i ⊢ ⚡={transmap_insert_inG t Ω}=> ownN i.
Proof.
  iIntros "Hwsat".
  rewrite /ownN.
  iApply transmap_own_insert_other_left.
  iFrame.
Qed.





Local Lemma transform_mono {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ) :
  (⚡={Ω}=> P) ⊢ ⚡={Ω}=> P.
Proof.
  apply nextgen_basic.bnextgen_mono.
  iIntros "HP";done.
Qed.

Local Lemma transform_later {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ) :
  (▷ ⚡={Ω}=> P) ⊢ ⚡={Ω}=> ▷ P.
Proof.
  rewrite nextgen_basic.bnextgen_later.
  auto.
Qed.

Local Lemma transform_plain {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ) :
  (■ P) ⊢ ⚡={Ω}=> ■ P.
Proof.
  iIntros "#HP".
  iApply nextgen_basic.bnextgen_intro_plainly. eauto.
Qed.

#[local] Instance insert_mono_into_pnextgen {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ)
  : IntoPnextgen Ω _ _ := transform_mono P.
#[local] Instance insert_later_into_pnextgen {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ)
  : IntoPnextgen Ω _ _ := transform_later P.
#[local] Instance insert_plain_into_pnextgen {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ)
  : IntoPnextgen Ω _ _ := transform_plain P.

Local Lemma map_imap_inv_pick_cut_coerce {A : cmra} `{pick: pick_transform_rel A} (c : C) (F : gmap positive (option C)) :
  pick_coerce <$> (map_imap (inv_pick_cut c) F) = map_imap (inv_pick_cut c) (pick_coerce <$> F).
Proof.
  induction F using map_ind.
  - rewrite fmap_empty map_imap_empty //.
  - rewrite fmap_insert !map_imap_insert.
    destruct (inv_pick_cut c i x) eqn:Hc.
    + rewrite fmap_insert.
      assert (inv_pick_cut c i (pick_coerce x) = Some (pick_coerce o)) as ->;[|rewrite IHF//].
      unfold inv_pick_cut.
      unfold inv_pick_cut in Hc.
      simpl. rewrite Hc. auto.
    + done.
Qed.

Local Lemma dom_map_imap_inv_pick_cut {Σ} {A : cmra} `{pick: pick_transform_rel A} (c : C) (I : gmap positive (iProp Σ)) (F : gmap positive (option C)) :
  dom I = dom F ->
  dom I = dom (map_imap (inv_pick_cut c) F).
Proof.
  intros Hdom.
  rewrite (dom_imap_L _ _ (dom I))//.
  intros i. split;intros Hi.
  - rewrite Hdom in Hi.
    apply elem_of_dom in Hi as [x Hx].
    exists x. split;eauto.
  - rewrite Hdom. apply elem_of_dom.
    destruct Hi as [x [Hx Hsome]]. eauto.
Qed.
    
Lemma wsat_ind_insert_intro `{!wsatGIndS Σ Ω A pick} (c : C) :
  wsat -∗ ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=> wsat.
Proof.
  iIntros "Hw". unfold wsat.
  rewrite -lock.
  iDestruct "Hw" as (I F Hdom) "[Hi [Hc H]]".
  iAssert ([∗ map] i↦Q ∈ I, ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=>
             ownN i ∨ (∃ c' : C, ownC i c' ∗ inv_cond Q c' ∗ (▷ Q ∗ ownD {[i]} ∨ ownE {[i]})))%I with "[H]" as "H".
  { iApply (big_sepM_mono with "H").
    iIntros (k x Hx) "[HN | HC]".
    - iDestruct (frag_pick_map_None_two_intro with "HN") as "HN".
      iModIntro. iLeft. iFrame.
    - iDestruct "HC" as (c') "[HC [#Hcond [[Hx HD] | HE]]]".
      + destruct (decide (CR c' c)).
        * iDestruct (frag_pick_map_transform_two_Some_intro with "HC") as "HC";[eauto|].
          iAssert (▷ ⚡={transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω}=> x)%I with "[Hx]" as "Hx".
          { iNext. iApply ("Hcond" with "[//] [$]"). }
          iDestruct (ownD_ind_insert_two_intro with "HD") as "HD".
          iModIntro.
          iRight. iExists c'. iFrame "Hcond HC". iLeft; iFrame.
        * iDestruct (frag_pick_map_transform_two_None_intro with "HC") as "HC";[eauto|].
          iClear "Hx Hcond HD". iModIntro. by iLeft.
      + destruct (decide (CR c' c)).
        * iDestruct (frag_pick_map_transform_two_Some_intro with "HC") as "HC";[eauto|].
          iDestruct (ownE_ind_insert_two_intro  _ (inv_pick_transform c) with "HE") as "HE".
          iModIntro. iRight. iExists c'. iFrame "Hcond HC". iRight. iFrame.
        * iDestruct (frag_pick_map_transform_two_None_intro with "HC") as "HC";[eauto|].
          iClear "HE Hcond". iModIntro. by iLeft. }
  rewrite transmap_big_sepM_1.
  iDestruct (auth_pick_map_transform_two_intro _ c with "Hc") as "Hc".
  iDestruct (auth_invariant_insert_two_intro _ (inv_pick_transform c) (C_pick c) with "Hi") as "Hi".
  iModIntro. iExists I,(map_imap (inv_pick_cut c) F). iFrame.
  rewrite map_imap_inv_pick_cut_coerce. iFrame.
  iPureIntro.
  apply dom_map_imap_inv_pick_cut=>//.
Qed.
