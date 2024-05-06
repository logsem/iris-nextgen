From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import wsat.
From nextgen.lib Require Export wsat.
From iris.base_logic Require Export later_credits.
From iris.prelude Require Import options.
Export wsatGS.
Import uPred.
Import le_upd_if.
From nextgen Require Import nextgen_pointwise.

(** The definition of fancy updates (and in turn the logic built on top of it) is parameterized
    by whether it supports elimination of laters via later credits or not.
    This choice is necessary as the fancy update *with* later credits does *not* support
    the interaction laws with the plainly modality in [BiFUpdPlainly]. While these laws are
    seldomly used, support for them is required for backwards compatibility.

    Thus, the [invGS_gen] typeclass ("gen" for "generalized") is parameterized by
    a parameter of type [has_lc] that determines whether later credits are
    available or not. [invGS] is provided as a convenient notation for the default [HasLc].
    We don't use that notation in this file to avoid confusion.
 *)

Class invGIndpreS (Σ : gFunctors) (Ω : gTransformations Σ) (A : cmra) (pick: pick_transform_rel A) : Set := InvGIndpreS {
  invGIndpreS_wsat : wsatGIndpreS Σ Ω A pick;
  invGIndpreS_lc : lcGIndpreS Σ Ω;
}.

Class invGIndS_gen (hlc : fancy_updates.has_lc) (Σ : gFunctors) (Ω : gTransformations Σ) (A : cmra) (pick: pick_transform_rel A) : Set := InvIndG {
  invGS_ind_wsat : wsatGIndS Σ Ω A pick;
  invGS_ind_lc : lcGIndS Σ Ω;
}.
Global Hint Mode invGIndS_gen - - - - - : typeclass_instances.
Global Hint Mode invGIndpreS - - - - : typeclass_instances.

Local Existing Instances invGIndpreS_wsat invGIndpreS_lc.
(* [invGS_lc] needs to be global in order to enable the use of lemmas like [lc_split]
   that require [lcGS], and not [invGS].
   [invGS_wsat] also needs to be global as the lemmas in [invariants.v] require it. *)
Global Existing Instances invGS_ind_lc invGS_ind_wsat.

#[global] Instance into_invpres `{Hinv: !invGIndpreS Σ Ω A pick} : fancy_updates.invGpreS Σ :=
  fancy_updates.InvGpreS Σ (@into_wsatpres A pick Σ Ω invGIndpreS_wsat) (@into_lcpres Σ Ω invGIndpreS_lc).

#[global] Instance into_invs `{Hinv: !invGIndS_gen hlc Σ Ω A pick} : fancy_updates.invGS_gen hlc Σ :=
  fancy_updates.InvG hlc Σ (@into_wsats A pick Σ Ω invGS_ind_wsat) (@into_lcs Σ Ω invGS_ind_lc).

Notation has_lc := fancy_updates.has_lc.
Notation HasLc := fancy_updates.HasLc.
Notation HasNoLc := fancy_updates.HasNoLc.
Notation ownE := wsat.ownE.
Notation ownD := wsat.ownD.
Notation ownI := wsat.ownI.

Notation invGIndS := (invGIndS_gen HasLc).

Local Definition uPred_fupd_def `{!invGIndS_gen hlc Σ Ω T pick} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 -∗ le_upd_if (if hlc is fancy_updates.HasLc then true else false) (◇ (wsat ∗ ownE E2 ∗ P)).
Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {hlc Σ _ _ _ _}.
Local Lemma uPred_fupd_unseal `{!invGIndS_gen hlc Σ Ω A pick} : @fupd _ uPred_fupd = uPred_fupd_def.
Proof. rewrite -uPred_fupd_aux.(seal_eq) //. Qed.

Lemma uPred_fupd_mixin `{!invGIndS_gen hlc Σ Ω A pick} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_unseal. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    by iIntros "($ & $ & HE) !> !> [$ $] !> !>".
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_unseal.
    iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_unseal. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_unseal /uPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite uPred_fupd_unseal /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance uPred_bi_fupd `{!invGIndS_gen hlc Σ Ω A pick} : BiFUpd (uPredI (iResUR Σ)) | 1 :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Global Instance uPred_bi_bupd_fupd {Σ : gFunctors} `{!invGIndS_gen hlc Σ Ω A pick} : BiBUpdFUpd (uPredI (iResUR Σ)) | 1.
Proof. rewrite /BiBUpdFUpd. rewrite uPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

(** The interaction laws with the plainly modality are only supported when
  we opt out of the support for later credits. *)
Global Instance uPred_bi_fupd_plainly_no_lc `{!invGIndS_gen fancy_updates.HasNoLc Σ Ω T pick} :
  BiFUpdPlainly (uPredI (iResUR Σ)) | 1.
Proof.
  split; rewrite uPred_fupd_unseal /uPred_fupd_def.
  - iIntros (E P) "H [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    by iFrame.
  - iIntros (E P Q) "[H HQ] [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - iIntros (E P) "H [Hw HE]".
    iAssert (▷ ◇ ■ P)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - iIntros (E A Φ) "HΦ [Hw HE]".
    iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.

(** Later credits: the laws are only available when we opt into later credit support.*)

(** [lc_fupd_elim_later] allows to eliminate a later from a hypothesis at an update.
  This is typically used as [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP".],
  where ["Hcredit"] is a credit available in the context and ["HP"] is the
  assumption from which a later should be stripped. *)
Lemma lc_fupd_elim_later `{!invGIndS_gen HasLc Σ Ω T pick} E P :
   £ 1 -∗ (▷ P) -∗ |={E}=> P.
Proof.
  iIntros "Hf Hupd".
  rewrite uPred_fupd_unseal /uPred_fupd_def.
  iIntros "[$ $]". iApply (le_upd_later with "Hf").
  iNext. by iModIntro.
Qed.

(** If the goal is a fancy update, this lemma can be used to make a later appear
  in front of it in exchange for a later credit.
  This is typically used as [iApply (lc_fupd_add_later with "Hcredit")],
  where ["Hcredit"] is a credit available in the context. *)
Lemma lc_fupd_add_later `{!invGIndS_gen HasLc Σ Ω T pick} E1 E2 P :
  £ 1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iApply (fupd_trans E1 E1).
  iApply (lc_fupd_elim_later with "Hf Hupd").
Qed.
