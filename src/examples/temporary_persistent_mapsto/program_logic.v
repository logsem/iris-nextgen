From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import lock.
From iris.prelude Require Import options.

From self Require Import nextgen_basic.

Section test.
  Context `{!heapGS_gen hlc Σ}.

  (* [id] for now as we'll just axiomatize the rules. *)
  Definition RO (P : iProp Σ) : iProp Σ := ⚡={id}=> P.

  Notation "<RO> P" := (RO P) (at level 20, right associativity): bi_scope.

  (* Removes anything read-only. *)
  Definition NO (P : iProp Σ) : iProp Σ := ⚡={id}=> P.

  Notation "<NO> P" := (NO P) (at level 20, right associativity): bi_scope.

  (* Reverts any frozen mapsto's not in [ℓs]. *)
  Definition RV (ℓs : gset loc) (P : iProp Σ) : iProp Σ := ⚡={id}=> P.

  (* mapsto _t_emporarily _r_ead _o_nly *)
  Definition mapsto_tro (ℓ : loc) (v : val) : iProp Σ.
  Proof. Admitted.

  Definition mapsto_frozen (ℓ : loc) (dq : dfrac) (v : val) : iProp Σ.
  Proof. Admitted.

  Lemma mapsto_tro_to_ro ℓ v :
    mapsto_tro ℓ v ⊢ <RO> ℓ ↦ v.
  Proof.
    iIntros "H". iModIntro.
  Admitted.

  Lemma mapsto_temp_ro ℓ dq v :
    ℓ ↦{dq} v ⊢ |==> mapsto_tro ℓ v ∗ mapsto_frozen ℓ dq v.
  Proof.
  Admitted.

  Lemma no_elim P : <NO> P ⊢ P.
  Proof. Admitted.

  Class Normal P := {
    is_normal : <RO> P ⊣⊢ P
  }.

End test.

#[global]
Notation "<RO> P" := (RO P) (at level 20, right associativity): bi_scope.

#[global]
Notation "<NO> P" := (NO P) (at level 20, right associativity): bi_scope.

Section weakestpre.
  Context `{!heapGS_gen hlc Σ}.

  Definition wp_tro : Wp _ _ _ _ := λ st E e Q, wp' st E e (λ v, <RO> (Q v))%I.

  Existing Instance wp_tro.

  Lemma wp_unfold s E e Φ :
    WP e @ s; E {{ Φ }} ⊣⊢ wp' s E e (λ v, <RO> Φ v).
  Proof. done. Qed.

  Lemma wp_strong_mono s1 s2 E1 E2 e Φ `{∀ v, Normal (Φ v)} Ψ `{∀ v, Normal (Ψ v)} :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
  Proof.
    rewrite !wp_unfold.
    intros ??. iIntros "? Hi".
    iApply (wp_strong_mono with "[$]"); [done|done| ].
    iIntros (?).
    rewrite 2!is_normal.
    done.
  Qed.

  Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
    WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
  Proof.
    rewrite !wp_unfold.
    iIntros "H".
    iApply wp_bind.
    iApply (wp_mono with "H").
  Admitted.

  Instance wp_normal Φ e :
    (∀ v, Normal (Φ v)) → Normal (WP e {{ Φ }}).
  Proof. Admitted.

  (* NOTE: [R] is not normal. *)
  Lemma wp_framed_bind K `{!LanguageCtx K} s E e
      Φ `{∀ v, Normal (Φ v)} (R : iProp Σ) :
    R ∗ WP e @ s; E {{ v, (R -∗ WP K (of_val v) @ s; E {{ Φ }}) }}
    ⊢ WP K e @ s; E {{ Φ }}.
  Proof.
    rewrite !wp_unfold.
    iIntros "[R Hwp]".
    (* Search "wp_bind". *)
    iApply wp_bind.
    iApply (wp_mono with "Hwp").
  Admitted.

  (* (* NOTE: [R] is not normal. *) *)
  (* Lemma wp_framed_bind_alt K `{!LanguageCtx K} s E e *)
  (*     Φ `{∀ v, Normal (Φ v)} (R : iProp Σ) : *)
  (*   R ∗ *)
  (*   WP e @ s; E {{ Q }} ∗ *)
  (*   (∀ v, R -∗ WP K (of_val v) @ s; E {{ Φ }}) *)
  (*   ⊢ WP K e @ s; E {{ Φ }}. *)
  (* Proof. *)
  (*   rewrite !wp_unfold. *)
  (*   iIntros "[R Hwp]". *)
  (*   Search "wp_bind". *)
  (*   iApply wp_bind. *)
  (*   iApply (wp_mono with "Hwp"). *)
  (* Qed. *)

End weakestpre.

Section weakestpre_attempt_2.
  Context `{!heapGS_gen hlc Σ}.

  Definition wp_tro_2 : Wp _ _ _ _ := λ st E e Q,
    (∀ (h : gmap loc val),
    RV (dom h) (
      ([∗ map] ℓ ↦ v ∈ h, mapsto_frozen ℓ (DfracOwn 1) v) -∗
      wp' st E e (λ v, RV (dom h) (
        ([∗ map] ℓ ↦ v ∈ h, mapsto_frozen ℓ (DfracOwn 1) v) ∗
        <NO> (Q v)))
    ))%I.

  Existing Instance wp_tro_2.

  (* Lemma wp_unfold_2 s E e Φ : *)
  (*   WP e @ s; E {{ Φ }} ⊣⊢ wp' s E e (λ v, <RO> Φ v). *)
  (* Proof. done. Qed. *)

  (* NOTE: [R] is not normal. *)
  Lemma wp_framed_bind_2 K `{!LanguageCtx K} s E e
      Φ `{∀ v, Normal (Φ v)} (R : iProp Σ) :
    R ∗ WP e @ s; E {{ v, (R -∗ WP K (of_val v) @ s; E {{ Φ }}) }}
    ⊢ WP K e @ s; E {{ Φ }}.
  Proof.
    rewrite /wp /wp_tro_2 /=.
    iIntros "[R H]" (h).
    iSpecialize ("H" $! h).
    iModIntro.
    (* "M". *)
    iSpecialize ("WP" with "M").
    iApply weakestpre.wp_bind.
    iApply (wp_mono with "WP").
    iIntros (v) "RV".
  Admitted.

End weakestpre_attempt_2.
