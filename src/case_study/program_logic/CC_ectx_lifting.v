(** Adapted from the Coq development of "Mechanized Relational
    Verification of Concurrent Programs with Continuations" ICFP '19

    Original author: Amin Timany *)

(** Some derived lemmas for ectx-based languages with continuations *)
From nextgen.case_study.program_logic Require Export weakestpre.
From nextgen.case_study.program_logic Require Export lifting.
From nextgen.case_study Require Export CC_ectx_language.
(* From nextgen Require Import nextgen_basic gmap_view_transformation. *)
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {expr val ectx state observation} {Λ : CCEctxLanguage expr val ectx state observation}.
Context `{irisGS_gen hls (CC_ectx_lang expr) Σ} {Hinh : Inhabited state}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Implicit Types κ κs : list observation.
Implicit Types ns nt : nat.
Hint Resolve head_prim_reducible
     head_nonthrow_prim_reducible
     head_normal_prim_reducible
     head_capture_prim_reducible
     head_throw_prim_reducible
     head_normal_reducible_prim_step
     head_capture_reducible_prim_step
     head_nonthrow_reducible_prim_step
     head_throw_reducible_prim_step : core.

Lemma wp_lift_nonthrow_head_step_fupdN {s E Φ} K e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, (⚡={next_state σ1}=> |==> state_interp σ1 ns (κ ++ κs) nt) ={E,∅}=∗
    ⌜head_nonthrow_reducible K e1 σ1⌝ ∗
    ∀ rm e2 σ2 efs, ⌜head_step K e1 σ1 κ e2 σ2 efs rm⌝ -∗
      £ (S (num_laters_per_step ns))
      ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
      (⚡={next_state σ2}=> |==> state_interp σ2 (S ns) κs (length efs + nt)) ∗ WP fill K e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupdN=>//; eauto using CC_fill_not_val.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs) "H1 Ht".
  iDestruct "H1" as %Hps.
  eapply head_nonthrow_reducible_prim_step in Hps; eauto.
  destruct Hps as (?&e2'&?&?&Hps); subst.
  iApply "H". by eauto. iFrame.
Qed.

Lemma wp_lift_nonthrow_head_step {s E Φ} K e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, (⚡={next_state σ1}=> |==> state_interp σ1 ns (κ ++ κs) nt) ={E,∅}=∗
    ⌜head_nonthrow_reducible K e1 σ1⌝ ∗
    ▷ ∀ rm e2 σ2 efs, ⌜head_step K e1 σ1 κ e2 σ2 efs rm⌝ -∗
      £ 1 ={∅,E}=∗ (⚡={next_state σ2}=> |==> state_interp σ2 (S ns) κs (length efs + nt)) ∗ WP fill K e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step=>//; eauto using CC_fill_not_val.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iNext. iIntros (e2 σ2 efs) "H1 Ht".
  iDestruct "H1" as %Hps.
  eapply head_nonthrow_reducible_prim_step in Hps; eauto.
  destruct Hps as (?&e2'&?&?&Hps); subst.
  iApply "H";eauto.
Qed.

Lemma wp_lift_throw_head_step_fupdN {s E Φ} K e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, (⚡={next_state σ1}=> |==> state_interp σ1 ns (κ ++ κs) nt) ={E,∅}=∗
    ⌜head_throw_reducible K e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step K e1 σ1 κ e2 σ2 efs ThrowMode⌝ -∗
      £ (S (num_laters_per_step ns))
      ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
      (⚡={next_state σ2}=> |==> state_interp σ2 (S ns) κs (length efs + nt)) ∗ WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupdN=>//; eauto using CC_fill_not_val.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs) "H1 Ht".
  iDestruct "H1" as %Hps.
  eapply head_throw_reducible_prim_step in Hps; eauto.
  iApply "H". by eauto. iFrame.
Qed.

Lemma wp_lift_throw_head_step {s E Φ} K e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, (⚡={next_state σ1}=> |==> state_interp σ1 ns (κ ++ κs) nt) ={E,∅}=∗
    ⌜head_throw_reducible K e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step K e1 σ1 κ e2 σ2 efs ThrowMode⌝ -∗
       £ 1 ={∅,E}=∗ (⚡={next_state σ2}=> |==> state_interp σ2 (S ns) κs (length efs + nt)) ∗ WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step=>//; eauto using CC_fill_not_val.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iNext. iIntros (e2 σ2 efs) "H1 Ht".
  iDestruct "H1" as %Hps.
  eapply head_throw_reducible_prim_step in Hps; eauto.
  iApply "H". by eauto. iFrame.
Qed.

Lemma wp_lift_nonthrow_pure_head_step_no_fork {s E E' Φ} K e1 :
  (∀ σ1, head_nonthrow_reducible K e1 σ1) →
  (∀ rm σ1 κ e2 σ2 efs, head_step K e1 σ1 κ e2 σ2 efs rm → κ = [] ∧ σ2 = σ1 /\ efs = []) →
  (|={E}[E']▷=> ∀ rm κ e2 efs σ, ⌜head_step K e1 σ κ e2 σ efs rm⌝ -∗ £ 1 -∗
    WP fill K e2 @ s; E {{ Φ }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof using Hinh.
  iIntros (Hnthsp Hpure) "H".
  iApply wp_lift_pure_step_no_fork;
    first destruct s; eauto.
  - intros σ; specialize (Hnthsp σ).
    eauto using reducible_not_val,
    head_prim_reducible, head_nonthrow_prim_reducible.
  - intros ? ? ? ? ? Hps.
    eapply head_nonthrow_reducible_prim_step in Hps; eauto.
    destruct Hps as (e2'&?&?&?&Hps); subst; eauto.
  - iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (???? Hps) "Ht".
    eapply head_nonthrow_reducible_prim_step in Hps; eauto.
    destruct Hps as (e2'&?&?&?&Hps); subst; eauto.
    iDestruct ("H" with "[] Ht") as "?";eauto.
Qed.

Lemma wp_lift_throw_pure_head_step_no_fork {s E E' Φ} K e1 :
  (∀ σ1, head_throw_reducible K e1 σ1) →
  (∀ rm σ1 κ e2 σ2 efs, head_step K e1 σ1 κ e2 σ2 efs rm → κ = [] /\ σ2 = σ1 /\ efs = []) →
  (|={E}[E']▷=> ∀ rm κ e2 efs σ, ⌜head_step K e1 σ κ e2 σ efs rm⌝ -∗ £ 1 -∗
    WP e2 @ s; E {{ Φ }})
  ⊢ WP fill K e1 @s;  E {{ Φ }}.
Proof using Hinh.
  iIntros (Hthsp Hpure) "H". iApply wp_lift_pure_step_no_fork; first destruct s; eauto.
  - intros σ; specialize (Hthsp σ).
    eauto using reducible_not_val,
    head_prim_reducible, head_throw_prim_reducible.
  - iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (???? Hps) "Ht".
    eapply head_throw_reducible_prim_step in Hps; eauto.
    iDestruct ("H" with "[] [$]") as "$"; eauto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. These we only show for non-throw
   operational steps as atomic throw steps don't happen in practice! *)
Lemma wp_lift_nonthrow_atomic_head_step {s E Φ} K e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, (⚡={next_state σ1}=> |==> state_interp σ1 ns (κ ++ κs) nt) ={E}=∗
    ⌜head_nonthrow_reducible K e1 σ1⌝ ∗
    ▷ ∀ rm e2 σ2 efs, ⌜head_step K e1 σ1 κ e2 σ2 efs rm⌝ -∗
      £ 1 ={E}=∗ (⚡={next_state σ2}=> |==> state_interp σ2 (S ns) κs (length efs + nt)) ∗
      from_option (λ v, WP fill K (of_val v) @ s; E {{Φ}}) False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_nonthrow_head_step)=>//; eauto using CC_fill_not_val.
  iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply (fupd_mask_intro E ∅);[set_solver|]. iIntros "Hclose".
  iNext; iIntros (rm e2 σ2 efs) "% Ht". iMod "Hclose" as "_".
  iMod ("H" $! rm e2 σ2 efs with "[#] Ht") as "($ & HΦ & $)"; auto.
  iModIntro.
  destruct (to_val e2) eqn:Heq; last by iExFalso.
  apply of_to_val in Heq; subst; auto.
Qed.

Lemma wp_lift_nonthrow_atomic_head_step_no_fork {s E Φ} K e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, (⚡={next_state σ1}=> |==> state_interp σ1 ns (κ ++ κs) nt) ={E}=∗
    ⌜head_nonthrow_reducible K e1 σ1⌝ ∗
    ▷ ∀ rm e2 σ2 efs, ⌜head_step K e1 σ1 κ e2 σ2 efs rm⌝ -∗ £ 1 ={E}=∗
      ⌜efs = []⌝ ∗ (⚡={next_state σ2}=> |==> state_interp σ2 (S ns) κs (length efs + nt)) ∗
      from_option (λ v, WP fill K (of_val v) @ s; E {{Φ}}) False (to_val e2))
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_nonthrow_atomic_head_step; eauto.
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (rm v2 σ2 efs) "% Ht".
  iMod ("H" $! rm v2 σ2 efs with "[# //] [$]") as "(% & $ & $)"; subst; auto.  
Qed.

Lemma wp_lift_nonthrow_pure_det_head_step_no_fork {s E E' Φ} K e1 e2 :
  (∀ σ1, head_nonthrow_reducible K e1 σ1) →
  (∀ σ1 κ e2' σ2 efs' rm,
    head_step K e1 σ1 κ e2' σ2 efs' rm → κ = [] /\ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> £ 1 -∗ WP fill K e2 @ s; E {{ Φ }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros Hnthsp Hdet.
  apply wp_lift_pure_det_step_no_fork; first destruct s; eauto; simpl.
  - intros σ; specialize (Hnthsp σ).
    eauto using reducible_not_val,
    head_prim_reducible, head_nonthrow_prim_reducible.
  - intros ????? Hps.
    apply head_nonthrow_reducible_prim_step in Hps; auto.
    destruct Hps as (?&?&?&?&Hhs); subst.
    apply Hdet in Hhs. destruct Hhs as (?&?&?);subst. intuition congruence.
Qed.

Lemma wp_lift_throw_pure_det_head_step_no_fork {s E E' Φ} K e1 e2 :
  (∀ σ1, head_throw_reducible K e1 σ1) →
  (∀ σ1 κ e2' σ2 efs' rm,
    head_step K e1 σ1 κ e2' σ2 efs' rm → κ = [] /\ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> £ 1 -∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros Hthsp Hdet. apply wp_lift_pure_det_step_no_fork; destruct s; eauto.
  intros σ; specialize (Hthsp σ).
    eauto using reducible_not_val,
    head_prim_reducible, head_throw_prim_reducible.
Qed.

Lemma wp_lift_nonthrow_pure_det_head_step_no_fork' {s E Φ} K e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_nonthrow_reducible K e1 σ1) →
  (∀ rm σ1 κ e2' σ2 efs',
    head_step K e1 σ1 κ e2' σ2 efs' rm → κ = [] /\ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ (£ 1 -∗ WP fill K e2 @ s; E {{ Φ }}) ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros.
  rewrite -[(WP (fill K e1) @ _; _ {{ _ }})%I]
             wp_lift_nonthrow_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
  intros. eauto.
Qed.

Lemma wp_lift_throw_pure_det_head_step_no_fork' {s E Φ} K e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_throw_reducible K e1 σ1) →
  (∀ rm σ1 κ e2' σ2 efs',
    head_step K e1 σ1 κ e2' σ2 efs' rm → κ = [] /\ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ (£ 1 -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP fill K e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros.
  rewrite -[(WP (fill K e1) @ _; _ {{ _ }})%I]
             wp_lift_throw_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //. intros;eauto.
Qed.

Lemma wp_atomic_under_ectx E1 E2 K e Φ :
  Atomic StronglyAtomic e → sub_values e → is_normal e →
  (|={E1,E2}=> WP e @ E2 {{ v, |={E2,E1}=> WP fill K (of_val v) @ E1 {{ Φ }} }})
    ⊢ WP fill K e @ E1 {{ Φ }}.
Proof.
  iIntros (Hatomic Hsv Hin) "H".
  iLöb as "IH" forall (e Hatomic Hsv Hin).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val (fill K e)) as [v|] eqn:HKe.
  - iMod "H".
    destruct (to_val e) as [e'|] eqn:Heqe'; last
      by eapply (CC_fill_not_val K) in Heqe'; rewrite Heqe' in HKe.
    repeat iMod "H".
    rewrite (of_to_val _ _ Heqe').
    iApply wp_value_fupd; simpl; eauto.
  - iIntros (σ1 ns κ κs nt) "Hσ". iMod "H".
    destruct (to_val e) as [v|] eqn:He.
    + do 2 iMod "H". rewrite (of_to_val _ _ He).
      rewrite !wp_unfold /wp_pre /= HKe.
      by iApply ("H" with "Hσ").
    + iMod ("H" with "Hσ") as "[Hr H]".
      iDestruct "Hr" as %Hr.
      iModIntro; iSplit; first by iPureIntro;
        auto using reducible_under_ectx.
      iIntros (e2 σ2 efs2) "Hps Ht". iDestruct "Hps" as %Hps.
      destruct (reducible_prim_step _ _ _ _ _ _ _ Hr Hsv Hin Hps) as
            (e2' & He2 & Hps'); simpl in *; subst.
      iDestruct ("H" with "[] Ht") as "HH";eauto.
      iMod "HH". iModIntro. iNext.
      iMod "HH". iModIntro.
      iDestruct (step_fupdN_frame_l with "[IH HH]") as "HH". iSplitR;[iExact "IH"|iFrame "HH"].
      iApply (step_fupdN_mono with "HH").
      iIntros "[IH HH]".
      destruct (to_val e2') as [z|] eqn:Heqz.
      ++ rewrite {1}wp_unfold /wp_pre /= Heqz /=.
         rewrite (of_to_val _ _ Heqz). iMod "HH" as "[? [HH ?]]". iApply fupd_frame_l.
         iFrame. iMod "HH". iFrame.
      ++ apply Hatomic in Hps'. simpl in Hps'. rewrite Heqz in Hps'.
         inversion Hps'. done.
Qed.

End wp.
