From stdpp Require Export coPset.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import wsat later_credits invariants.
From iris.prelude Require Import options.

From nextgen Require Import nextgen_pointwise.
  
(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [wsatGS] module. The module [wsatGS] is thus exported in
[fancy_updates], where [wsat] is only imported. *)
Module wsatGS.

Class wsatGIndpreS (Σ : gFunctors) (Ω : gTransformations Σ) : Set := WsatGIndpreS {
  wsatGpreS_inv : genIndInG Σ Ω (gmap_viewR positive (laterO (iPropO Σ)));
  wsatGpreS_enabled : genIndInG Σ Ω coPset_disjR;
  wsatGpreS_disabled : genIndInG Σ Ω (gset_disjR positive);
}.

Class wsatGIndS (Σ : gFunctors) (Ω : gTransformations Σ) : Set := WsatGInd {
  wsat_inG : wsatGIndpreS Σ Ω;
  invariant_name : gname;
  enabled_name : gname;
  disabled_name : gname;
}.
Global Hint Mode wsatGIndpreS - - : typeclass_instances.
Global Hint Mode wsatGIndS - - : typeclass_instances.


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



#[global] Instance into_wsatpres `{Hwsat: wsatGIndpreS Σ Ω} : wsatGpreS Σ :=
  WsatGpreS Σ wsatGpreS_inv.(genInG_inG) wsatGpreS_enabled.(genInG_inG) wsatGpreS_disabled.(genInG_inG).
  
#[global] Instance into_wsats `{Hwsat: wsatGIndS Σ Ω} : wsatGS Σ :=
  WsatG Σ (@into_wsatpres Σ Ω wsat_inG) invariant_name enabled_name disabled_name.

#[global] Instance into_lcpres `{Hlc: lcGIndpreS Σ Ω} : lcGpreS Σ :=
  LcGpreS Σ lcGpreS_inG.(genInG_inG).

#[global] Instance into_lcs `{Hlc: lcGIndS Σ Ω} : lcGS Σ :=
  LcGS Σ lcGS_inG.(genInG_inG) lcGS_name.

Definition inv_cond `{!wsatGIndS Σ Ω} `{!noTransInG Σ Ω T} Q : iProp Σ := ■ (∀ (f : T → T) `{!CmraMorphism f}, Q -∗ ⚡={transmap_insert_inG f Ω}=> Q).

Definition wsat `{!wsatGIndS Σ Ω} `{!noTransInG Σ Ω T} : iProp Σ :=
  locked (∃ I : gmap positive (iProp Σ),
    own invariant_name (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
    [∗ map] i ↦ Q ∈ I, inv_cond Q ∗ ((▷ Q ∗ ownD {[i]}) ∨ ownE {[i]}))%I.

Section wsat.
Context `{!wsatGIndS Σ Ω} `{!noTransInG Σ Ω T}.
Implicit Types P : iProp Σ.

Lemma ownI_open i P : wsat ∗ ownI i P ∗ ownE {[i]} ⊢ wsat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HiE)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[#Hcond [[HQ $]|HiE']] HI]"; eauto.
  - iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
    iExists I. iFrame "Hw". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma ownI_close i P : wsat ∗ ownI i P ∗ ▷ P ∗ ownD {[i]} ⊢ wsat ∗ ownE {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[#?[[HQ ?]|$]] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iFrame "Hw". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI #". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma ownI_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  inv_cond P ∗
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P.
Proof.
  iIntros (Hfresh) "[#Hcond [Hw HP]]". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI #". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_open φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  inv_cond P ∗ wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ wsat) ∗ ownI i P ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "[#Hcond Hw]". rewrite /wsat -!lock. iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  unfold ownD. simpl. iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI #". by iRight.
Qed.
End wsat.

(* Allocation of an initial world *)
Lemma wsat_alloc `{!wsatGIndpreS Σ Ω} `{!noTransInG Σ Ω T} : ⊢ |==> ∃ _ : wsatGIndS Σ Ω, wsat ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatGInd _ _ _ γI γE γD).
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.

Lemma lc_ind_insert_intro `{lcGIndS Σ Ω} `{noTransInG Σ Ω A} (m : nat) (t : A → A) `{!CmraMorphism t} :
  £ m ⊢ ⚡={transmap_insert_inG t Ω}=> £ m.
Proof.
  iIntros "Hm".
  unfold lc. rewrite seal_eq /= /later_credits.lc_def /=.
  iModIntro. iFrame.
Qed.

#[global]
Instance lc_into_pnextgen `{lcGIndS Σ Ω} `{noTransInG Σ Ω A}
    (m : nat) (t : A → A) `{!CmraMorphism t} : IntoPnextgen _ _ _ :=
  lc_ind_insert_intro m t.

Lemma lc_ind_intro `{lcGIndS Σ Ω} (m : nat) :
  £ m -∗ ⚡={Ω}=> £ m.
Proof.
  iIntros "Hm".
  unfold lc. rewrite seal_eq /= /later_credits.lc_def /=.
  iModIntro. iFrame.
Qed.

Lemma ownE_ind_insert_intro `{wsatGIndS Σ Ω} `{noTransInG Σ Ω A} (E: coPset) (t : A → A) `{!CmraMorphism t} :
  ownE E -∗ ⚡={transmap_insert_inG t Ω}=> ownE E.
Proof.
  iIntros "Hwsat".
  unfold ownE.
  iModIntro. iFrame.
Qed.

Lemma ownE_ind_intro `{wsatGIndS Σ Ω} (E: coPset) :
  ownE E -∗ ⚡={Ω}=> ownE E.
Proof.
  iIntros "Hwsat".
  unfold ownE.
  iModIntro. iFrame.
Qed.

Lemma ownD_ind_insert_intro `{wsatGIndS Σ Ω} `{noTransInG Σ Ω A} (E: gset positive) (t : A → A) `{!CmraMorphism t} :
  ownD E -∗ ⚡={transmap_insert_inG t Ω}=> ownD E.
Proof.
  iIntros "Hwsat".
  unfold ownD.
  iModIntro. iFrame.
Qed.

Lemma ownD_ind_intro `{wsatGIndS Σ Ω} (E: gset positive) :
  ownD E -∗ ⚡={Ω}=> ownD E.
Proof.
  iIntros "Hwsat".
  unfold ownD.
  iModIntro. iFrame.
Qed.

Lemma wsat_ind_insert_intro `{wsatGIndS Σ Ω} `{noTransInG Σ Ω A} (t : A → A) `{!CmraMorphism t} :
  wsat -∗ ⚡={transmap_insert_inG t Ω}=> wsat.
Proof.
  iIntros "Hw". unfold wsat.
  rewrite -lock.
  iDestruct "Hw" as (I) "[Hi H]".
  iAssert ([∗ map] i↦Q ∈ I, ⚡={transmap_insert_inG t Ω}=> inv_cond Q ∗ (▷ Q ∗ ownD {[i]} ∨ ownE {[i]}))%I with "[H]" as "H".
  { iApply (big_sepM_mono with "H").
    iIntros (k x Hx) "[#Hcond [[Hx Hi]|Hi]]".
    - iAssert (▷ ⚡={transmap_insert_inG t Ω}=> x)%I with "[Hx]" as "Hx".
      { iNext. by iApply "Hcond". }
      iDestruct (ownD_ind_insert_intro with "Hi") as "Hi".
      iModIntro. iFrame "#". iLeft. iFrame.
    - iDestruct (ownE_ind_insert_intro with "Hi") as "Hi".
      iModIntro. iFrame "#". iRight. iFrame. }
  iDestruct (transmap_big_sepM_1 with "H") as "H".
  iModIntro. iExists _. iFrame.
Qed.
