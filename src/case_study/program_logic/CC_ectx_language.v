(** Adapted from the Coq development of "Mechanized Relational
    Verification of Concurrent Programs with Continuations" ICFP '19

    Original author: Amin Timany *)

(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.algebra Require Export ofe.
From iris.program_logic Require Import language.
Set Default Proof Using "Type".

(* Whether reduction is a normal reduction, it is a throw reduction or
a capture reduction where the evaluation context is captured *)
Inductive RedMode :=  NormalMode | CaptureMode | ThrowMode.

(* We need to make thos arguments indices that we want canonical structure
   inference to use a keys. *)
Class CCEctxLanguage (expr val ectx state observation : Type) := {
  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : ectx → expr → state → list observation -> expr → state → list expr → RedMode → Prop;
  capture : ectx → expr → option expr;

  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck K e1 σ1 κ e2 σ2 rm efs :
    head_step K e1 σ1 κ e2 σ2 efs rm → to_val e1 = None;

  CC_fill_empty e : fill empty_ectx e = e;
  CC_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
  CC_fill_inj K :> Inj (=) (=) (fill K);
  CC_fill_not_val K e : to_val e = None → to_val (fill K e) = None;

  (* Many axioms probably make sense here. In ectx_languages in Iris
  composition is only require to be positive. Here we require that
  composition is increasing. *)
  ectx_comp_increasing K1 K2 K1' K2' :
    K1 = comp_ectx K2 K2' → K2 = comp_ectx K1 K1' → K1 = K2;

  step_by_val gK K K' e1 e1' σ1 κ e2 σ2 efs rm :
    fill K e1 = fill K' e1' →
    to_val e1 = None →
    head_step gK e1' σ1 κ e2 σ2 efs rm →
    ∃ K'', K' = comp_ectx K K'';

  red_mode_det K e1 σ1 κ e2 σ2 efs rm :
    head_step K e1 σ1 κ e2 σ2 efs rm →
    ∀ K' σ1' e2' σ2' κ' efs' rm',
      head_step K' e1 σ1' κ' e2' σ2' efs' rm' → rm' = rm;

  ectx_capture_captures K e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs CaptureMode →
    capture K e1 = Some e2;

  ectx_normal_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs NormalMode →
    head_step K' e1 σ1 κ e2 σ2 efs NormalMode;

  ectx_capture_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs CaptureMode →
    ∃ e2', capture K' e1 = Some e2' ∧
           head_step K' e1 σ1 κ e2' σ2 efs CaptureMode;

  ectx_throw_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs ThrowMode →
    head_step K' e1 σ1 κ e2 σ2 efs ThrowMode
}.

Arguments of_val {_ _ _ _ _ _} _.
Arguments to_val {_ _ _ _ _ _} _.
Arguments empty_ectx {_ _ _ _ _ _}.
Arguments comp_ectx {_ _ _ _ _ _} _ _.
Arguments fill {_ _ _ _ _ _} _ _.
Arguments head_step {_ _ _ _ _ _} _ _ _ _ _ _ _.

Arguments to_of_val {_ _ _ _ _ _} _.
Arguments of_to_val {_ _ _ _ _ _} _ _ _.
Arguments val_stuck {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _.
Arguments CC_fill_empty {_ _ _ _ _ _} _ .
Arguments CC_fill_comp {_ _ _ _ _ _} _ _ _.
Arguments CC_fill_not_val {_ _ _ _ _ _} _ _ _.
Arguments step_by_val {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Arguments ectx_comp_increasing {_ _ _ _ _ _} _ _ _ _.
Arguments ectx_capture_captures {_ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments red_mode_det {_ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments ectx_normal_reduciblity {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _.
Arguments ectx_capture_reduciblity {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _.
Arguments ectx_throw_reduciblity {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _.

(* From a CC_ectx_language, we can construct a language. *)
Section CC_ectx_language.
  Context {expr val ectx state observation} {Λ : CCEctxLanguage expr val ectx state observation}.
  Implicit Types (e : expr) (K : ectx).

  Lemma step_by_both_vals
        K K' gK gK' e1 σ1 κ e2 σ2 efs rm e1' σ1' κ' e2' σ2' efs' rm':
    fill K e1 = fill K' e1' → head_step gK e1 σ1 κ e2 σ2 efs rm →
    head_step gK' e1' σ1' κ' e2' σ2' efs' rm' → K = K'.
  Proof.
    intros Heq Hstp Hstp'.
    edestruct (step_by_val gK' K K'); eauto using val_stuck.
    edestruct (step_by_val gK K' K); eauto using val_stuck.
    eapply ectx_comp_increasing; eauto.
  Qed.

  Definition head_reducible (K : ectx) (e : expr) (σ : state) :=
    ∃ e' σ' κ efs b, head_step K e σ κ e' σ' efs b.
  Definition head_irreducible (K : ectx) (e : expr) (σ : state) :=
    ∀ e' σ' κ efs b, ¬head_step K e σ κ e' σ' efs b.

  Definition sub_values (e : expr) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (e1 : expr) (σ1 : state) (κs : list observation)
      (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
  | Ectx_normal_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step K e1' σ1 κs e2' σ2 efs NormalMode → prim_step e1 σ1 κs e2 σ2 efs
  | Ectx_capture_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step K e1' σ1 κs e2' σ2 efs CaptureMode → prim_step e1 σ1 κs e2 σ2 efs
  | Ectx_throw_step K e1' :
      e1 = fill K e1' →
      head_step K e1' σ1 κs e2 σ2 efs ThrowMode → prim_step e1 σ1 κs e2 σ2 efs.

  Lemma Ectx_normal_step' K e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs NormalMode →
    prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Lemma Ectx_capture_step' K e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs CaptureMode →
    prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
  Proof. econstructor 2; eauto. Qed.

  Lemma Ectx_throw_step' K e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs ThrowMode →
    prim_step (fill K e1) σ1 κ e2 σ2 efs.
  Proof. econstructor 3; eauto. Qed.

  Lemma val_prim_stuck e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof.
    intros [??? -> -> ?|??? -> -> ?|?? -> ?]; eauto using CC_fill_not_val, val_stuck.
  Qed.

  Canonical Structure CC_ectx_langmixin : LanguageMixin of_val to_val prim_step :=
    {|
      language.mixin_to_of_val := to_of_val;
      language.mixin_of_to_val := of_to_val;
      language.mixin_val_stuck := val_prim_stuck
    |}.

  Canonical Structure CC_ectx_lang : language := {|
    language.expr := expr; language.val := val; language.state := state;
    language.of_val := of_val; language.to_val := to_val;
    language.prim_step := prim_step;
    language.language_mixin := CC_ectx_langmixin
  |}.

  Lemma reducible_under_ectx K e σ : reducible e σ → reducible (fill K e) σ.
  Proof.
    intros (e'&σ'&κ&efs'&Hrd); simpl in *.
    inversion Hrd; subst; rewrite CC_fill_comp.
    - rewrite /reducible /=; eauto 10 using ectx_normal_reduciblity, prim_step.
    - match goal with
        H : head_step _ _ _ _ _ _ _ _ |- _ =>
        eapply ectx_capture_reduciblity in H; firstorder
      end.
      rewrite /reducible /=; eauto 10 using prim_step.
    - rewrite /reducible /=; eauto 10 using ectx_throw_reduciblity, prim_step.
  Qed.

  Lemma not_head_reducible K e σ :
    ¬head_reducible K e σ ↔ head_irreducible K e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  Lemma head_prim_reducible K e σ :
    head_reducible K e σ → reducible (fill K e) σ.
  Proof. intros (e'&σ'&κ&efs&[| |]&Hred).
         - eexists _,(fill K e'), σ', efs. by apply Ectx_normal_step'.
         - eexists _,(fill K e'), σ', efs. by apply Ectx_capture_step'.
         - eexists _,e', σ', efs. by apply (Ectx_throw_step').
  Qed.
  Lemma head_prim_irreducible K e σ :
    irreducible (fill K e) σ → head_irreducible K e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible K e σ :
    reducible e σ → sub_values e → head_reducible K e σ.
  Proof.
    intros (e'&σ'&κ&efs&[K' e1' e2' -> -> Hstep|
                       K' e1' e2' -> -> Hstep|K' e1' -> Hstep]) Hsv.
    - assert (K' = empty_ectx) as -> by eauto 10 using val_stuck.
      apply (ectx_normal_reduciblity _ K) in Hstep.
      rewrite CC_fill_empty /head_reducible; repeat eexists; eauto.
    - assert (K' = empty_ectx) as -> by eauto 10 using val_stuck.
      apply (ectx_capture_reduciblity _ K) in Hstep.
      destruct Hstep as (e3 & He3 & Hstep).
      rewrite CC_fill_empty /head_reducible; repeat eexists; eauto.
    - assert (K' = empty_ectx) as -> by eauto 10 using val_stuck.
      apply (ectx_throw_reduciblity _ K) in Hstep.
      rewrite CC_fill_empty /head_reducible; repeat eexists; eauto.
  Qed.
  Lemma prim_head_irreducible K e σ :
    head_irreducible K e σ → sub_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma ectx_language_atomic a e :
    (∀ K σ e' σ' κ efs b,
        head_step K e σ κ e' σ' efs b →
        match a with
        | StronglyAtomic => is_Some (language.to_val e')
        | WeaklyAtomic => irreducible e' σ'
        end) →
    sub_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' σ' κ efs
           [K e1' e2' -> -> Hstep|K e1' e2' -> -> Hstep|K e1' -> Hstep].
    - assert (K = empty_ectx) as -> by eauto 10 using val_stuck.
      rewrite CC_fill_empty. eapply Hatomic_step. by rewrite CC_fill_empty.
    - assert (K = empty_ectx) as -> by eauto 10 using val_stuck.
      rewrite CC_fill_empty. eapply Hatomic_step. by rewrite CC_fill_empty.
    - assert (K = empty_ectx) as -> by eauto 10 using val_stuck.
      eapply Hatomic_step. by rewrite CC_fill_empty.
  Qed.

  Definition is_normal e :=
    ∀ K σ e' σ' κ efs rm, head_step K e σ κ e' σ' efs rm → rm = NormalMode.

  Lemma reducible_prim_step K e1 σ1 e2 σ2 κ efs:
    reducible e1 σ1 → sub_values e1 → is_normal e1 →
    prim_step (fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ prim_step e1 σ1 κ e2' σ2 efs.
  Proof.
    intros Hrdb Hsv Hin Hpr.
    edestruct (prim_head_reducible K) as (eh&σh&κs&efsh&rm&Hh); eauto.
    destruct Hpr as [K' e1' e2' Heq1 Heq2 Hstep|K' e1' e2' Heq1 Heq2 Hstep|
            K' e1' Heq Hstep]; subst.
    - erewrite <- (step_by_both_vals K K'); eauto.
      erewrite <- (step_by_both_vals K K') in Hstep; eauto.
      erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      eapply (ectx_normal_reduciblity _ empty_ectx) in Hstep.
      eexists; split; eauto.
      econstructor; eauto using CC_fill_empty.
    - erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      by apply Hin in Hstep.
    - erewrite (step_by_both_vals K K') in Heq; eauto.
      apply CC_fill_inj in Heq; subst.
      by apply Hin in Hstep.
  Qed.

  Inductive NonThrow : RedMode → Prop :=
  | NonThrow_Normal : NonThrow NormalMode
  | NonThrow_Capture : NonThrow CaptureMode.

  Definition head_nonthrow_reducible (K : ectx) (e : expr) (σ : state) :=
  ∃ rm e' σ' κ efs, NonThrow rm ∧ head_step K e σ κ e' σ' efs rm.
  Lemma head_nonthrow_prim_reducible K e σ :
    head_nonthrow_reducible K e σ → head_reducible K e σ.
  Proof.
    rewrite /head_nonthrow_reducible /head_reducible; firstorder; eauto.
    repeat eexists;eauto.
  Qed.

  Definition head_normal_reducible (K : ectx) (e : expr) (σ : state) :=
  ∃ e' σ' κ efs, head_step K e σ κ e' σ' efs NormalMode.
  Lemma head_normal_prim_reducible K e σ :
    head_normal_reducible K e σ → head_reducible K e σ.
  Proof. rewrite /head_normal_reducible /head_reducible; firstorder; repeat eexists; eauto. Qed.

  Definition head_capture_reducible (K : ectx) (e : expr) (σ : state) :=
  ∃ e' σ' κ efs, head_step K e σ κ e' σ' efs CaptureMode.
  Lemma head_capture_prim_reducible K e σ :
    head_capture_reducible K e σ → head_reducible K e σ.
  Proof. rewrite /head_normal_reducible /head_reducible; firstorder; repeat eexists; eauto. Qed.

  Definition head_throw_reducible (K : ectx) (e : expr) (σ : state) :=
  ∃ e' σ' κ efs, head_step K e σ κ e' σ' efs ThrowMode.
  Lemma head_throw_prim_reducible K e σ :
    head_throw_reducible K e σ → head_reducible K e σ.
  Proof. rewrite /head_throw_reducible /head_reducible; firstorder; repeat eexists; eauto. Qed.

  Lemma head_normal_reducible_prim_step K e1 σ1 e2 σ2 κ efs:
    head_normal_reducible K e1 σ1 →
    prim_step (fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ head_step K e1 σ1 κ e2' σ2 efs NormalMode.
  Proof.
    intros (e2''&σ2''&κs''&efs''&Hhs).
    pose proof (red_mode_det _ _ _ _ _ _ _ _ Hhs) as Hrm.
    intros [K' e1' e2' Heq1 Heq2 Hstep|K' e1' e2' Heq1 Heq2 Hstep|
            K' e1' Heq Hstep]; subst.
    - erewrite <- (step_by_both_vals K K'); eauto.
      erewrite <- (step_by_both_vals K K') in Hstep; eauto.
      erewrite (step_by_both_vals K K') in Heq1;
        eauto using ectx_normal_reduciblity.
      apply CC_fill_inj in Heq1; subst; eauto.
    - erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      by apply Hrm in Hstep.
    - erewrite (step_by_both_vals K K') in Heq; eauto.
      apply CC_fill_inj in Heq; subst.
      by apply Hrm in Hstep.
  Qed.

  Lemma head_capture_reducible_prim_step K e1 σ1 e2 σ2 κ efs:
    head_capture_reducible K e1 σ1 →
    prim_step (fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2', capture K e1 = Some e2' ∧ e2 = fill K e2' ∧
           head_step K e1 σ1 κ e2' σ2 efs CaptureMode.
  Proof.
    intros (e2''&σ2''&κs''&efs''&Hhs).
    pose proof (red_mode_det _ _ _ _ _ _ _ _ Hhs) as Hrm.
    intros [K' e1' e2' Heq1 Heq2 Hstep|K' e1' e2' Heq1 Heq2 Hstep|
            K' e1' Heq Hstep]; subst.
    - erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      by apply Hrm in Hstep.
    - erewrite <- (step_by_both_vals K K'); eauto.
      erewrite <- (step_by_both_vals K K') in Hstep; eauto.
      erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      rewrite (ectx_capture_captures _ _ _ _ _ _ _ Hstep); eauto.
    - erewrite (step_by_both_vals K K') in Heq; eauto.
      apply CC_fill_inj in Heq; subst.
      by apply Hrm in Hstep.
  Qed.

  Lemma head_nonthrow_reducible_prim_step K e1 σ1 e2 σ2 κ efs:
    head_nonthrow_reducible K e1 σ1 →
    prim_step (fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2' rm, e2 = fill K e2' ∧ NonThrow rm ∧
          head_step K e1 σ1 κ e2' σ2 efs rm.
  Proof.
    intros (rm&e2''&σ2''&κs''&efs''&Hnt&Hhs) Hps.
    destruct Hnt.
    - eapply head_normal_reducible_prim_step in Hps;
        last rewrite /head_normal_reducible; firstorder eauto.
    - eapply head_capture_reducible_prim_step in Hps;
        last rewrite /head_normal_reducible; firstorder eauto.
  Qed.

  Lemma head_throw_reducible_prim_step K e1 σ1 e2 σ2 κ efs:
    head_throw_reducible K e1 σ1 →
    prim_step (fill K e1) σ1 κ e2 σ2 efs →
    head_step K e1 σ1 κ e2 σ2 efs ThrowMode.
  Proof.
    intros (e2''&σ2''&κs''&efs''&Hhs).
    pose proof (red_mode_det _ _ _ _ _ _ _ _ Hhs) as Hrm.
    intros [K' e1' e2' Heq1 Heq2 Hstep|K' e1' e2' Heq1 Heq2 Hstep|
            K' e1' Heq Hstep]; subst.
    - erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      by apply Hrm in Hstep.
    - erewrite (step_by_both_vals K K') in Heq1; eauto.
      apply CC_fill_inj in Heq1; subst.
      by apply Hrm in Hstep.
    - erewrite <- (step_by_both_vals K K') in Hstep; eauto.
      erewrite (step_by_both_vals K K') in Heq; eauto.
      apply CC_fill_inj in Heq; subst; eauto.
  Qed.

End CC_ectx_language.

Arguments CC_ectx_lang _ {_ _ _ _ _}.
#[export] Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

#[export] Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.
