From iris.algebra Require Import functions gmap agree excl csum.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.
From iris.bi Require Import plainly.
From iris.bi Require Import derived_laws_later.

Import EqNotations. (* Get the [rew] notation. *)

#[global]
(* The functor in [Σ] at index [i] applied to [iProp]. *)
Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).

(* The functor in [Σ] at index [i] applied to [iPreProp]. *)
#[global]
Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).

Definition map_unfold {Σ} {i : gid Σ} : R Σ i -n> Rpre Σ i :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Definition map_fold {Σ} {i : gid Σ} : Rpre Σ i -n> R Σ i :=
  rFunctor_map _ (iProp_unfold, iProp_fold).

Lemma map_unfold_inG_unfold {Σ A} {i : inG Σ A} :
  map_unfold ≡ own.inG_unfold (i := i).
Proof. done. Qed.

Lemma map_fold_unfold {Σ} {i : gid Σ} (a : R Σ i) :
  map_fold (map_unfold a) ≡ a.
Proof.
  rewrite /map_fold /map_unfold -rFunctor_map_compose -{2}[a]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_fold_unfold.
Qed.

(** Transport an endo map on a camera along an equality in the camera. *)
Definition cmra_map_transport {A B : cmra}
    (Heq : A = B) (f : A → A) : (B → B) :=
  eq_rect A (λ T, T → T) f _ Heq.

Class Idemp {A} (R : relation A) (f : A -> A) : Prop :=
  idemp x : R (f (f x)) (f x).
Class Indep {A} (R : relation A) (f : A -> A) (g : A -> A) : Prop :=
  indep x : R (f (g x)) (g (f x)).
Class OIndep {A} (R : relation (option A)) (f : A -> option A) (g : A -> option A) : Prop :=
  oindep (x : A) : R (f x ≫= g) (g x ≫= f).

Section cmra_map_transport.
  Context {A B : cmra} (eq : A = B).

  #[global]
  Instance cmra_map_transport_ne' f :
    NonExpansive f →
    NonExpansive (cmra_map_transport (A := A) (B := B) eq f).
  Proof. solve_proper. Qed.

  Lemma cmra_map_transport_cmra_transport
      (f : A → A) a :
    (cmra_map_transport eq f) (cmra_transport eq a) =
    (cmra_transport eq (f a)).
  Proof. destruct eq. simpl. reflexivity. Defined.

  Global Instance cmra_map_transport_proper (f : A → A) :
    (Proper ((≡) ==> (≡)) f) →
    (Proper ((≡) ==> (≡)) (cmra_map_transport eq f)).
  Proof. naive_solver. Qed.

  Lemma cmra_map_transport_compose (f : A -> A) (g : A -> A) `{!CmraMorphism f} `{!CmraMorphism g} x :
    cmra_map_transport eq f (cmra_map_transport eq g x) = cmra_map_transport eq (f ∘ g) x.
  Proof. destruct eq. simpl. auto. Defined.

  Lemma cmra_map_transport_op f `{!CmraMorphism f} x y :
    cmra_map_transport eq f (x ⋅ y) ≡
      cmra_map_transport eq f x ⋅ cmra_map_transport eq f y.
  Proof. destruct eq. simpl. apply: cmra_morphism_op. Qed.

  Lemma cmra_map_transport_validN n f `{!CmraMorphism f} a :
    ✓{n} a → ✓{n} cmra_map_transport eq f a.
  Proof. destruct eq. apply: cmra_morphism_validN. Qed.

  Lemma cmra_map_transport_pcore f `{!CmraMorphism f} x :
    cmra_map_transport eq f <$> pcore x ≡ pcore (cmra_map_transport eq f x).
  Proof. destruct eq. simpl. apply: cmra_morphism_pcore. Qed.

  #[global]
  Instance gen_trans_cmra_map_transport (f : A → A) :
    CmraMorphism f → CmraMorphism (cmra_map_transport eq f).
  Proof. destruct eq. done. Qed.

  #[global]
   Instance idemP_cmra_map_transport (f : A -> A) :
    IdemP equiv (λ x _, f x) ->
    IdemP equiv (λ x _, (cmra_map_transport eq f) x).
  Proof. destruct eq. done. Qed.

  #[global]
   Instance idemp_cmra_map_transport (f : A -> A) :
    Idemp equiv f ->
    Idemp equiv (cmra_map_transport eq f).
  Proof. destruct eq. done. Qed.
  
End cmra_map_transport.

Lemma löb_wand_plainly {M} (P : uPredI M) `{!Absorbing P} :
    ■ ((■ ▷ P) -∗ P) ⊢ P.
Proof.
  rewrite -{3}(plainly_elim P) -(bi.löb (■ P)%I).
  apply bi.impl_intro_l. rewrite later_plainly_1.
  rewrite -{1}(plainly_idemp (▷ P)).
  rewrite -plainly_and plainly_and_sep. rewrite bi.wand_elim_r. auto.
Qed.

Lemma löb_wand_plainly_and_intuitionistically {M} (P : uPredI M) `{!Absorbing P} :
  □ ■ ((□ ■ ▷ P) -∗ P) ⊢ P.
Proof.
  rewrite -{3}(plainly_elim P) -{1}(bi.intuitionistically_elim (■ P)%I) -(bi.löb (□ ■ P)%I).
  apply bi.impl_intro_l. rewrite bi.later_intuitionistically later_plainly_1.
  rewrite -{1}(plainly_idemp (▷ P)).
  rewrite -{1}(bi.intuitionistically_idemp (■ ■ ▷ P)%I).
  rewrite intuitionistically_plainly.
  rewrite bi.and_sep_intuitionistically.
  rewrite bi.intuitionistically_sep_2 -plainly_sep. rewrite bi.wand_elim_r. auto.
Qed.

Lemma map_imap_ext `{FinMap K M} {A1 A2 B} `{Equiv B}
  (f1 : K → A1 → option B)
  (f2 : K → A2 → option B) (m1 : M A1) (m2 : M A2) :
  (∀ k, f1 k <$> (m1 !! k) ≡ f2 k <$> (m2 !! k)) →
  map_imap f1 m1 ≡ map_imap f2 m2.
Proof.
  intros HExt. intros i. (* apply map_equiv. intros i. *) rewrite !map_lookup_imap.
  specialize (HExt i). destruct (m1 !! i), (m2 !! i); simpl in *; inversion HExt; auto.
  apply None_equiv_eq. auto.
Qed.
