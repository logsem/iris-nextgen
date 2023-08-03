From iris.algebra Require Import functions gmap agree excl csum.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

Import EqNotations. (* Get the [rew] notation. *)

From self Require Import nextgen_basic.

#[global]
(* The functor in [Σ] at index [i] applied to [iProp]. *)
Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).

(* The functor in [Σ] at index [i] applied to [iPreProp]. *)
#[global]
Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).

Local Definition map_unfold {Σ} {i : gid Σ} : R Σ i -n> Rpre Σ i :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Local Definition map_fold {Σ} {i : gid Σ} : Rpre Σ i -n> R Σ i :=
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

End cmra_map_transport.

(** [TransMap] contains transformation functions for a subset of ghost names.
 * It is the entries that we have picked generational transformation for. *)
Definition TransMap Σ : Type := ∀ i, gmap gname (R Σ i → R Σ i).

Section nextgen_pointwise.
  Context `{Σ : gFunctors}.

  (* Build a global generational transformation based on the transformations in
   * [trans]. *)
  Definition build_trans (trans : TransMap Σ) : (iResUR Σ → iResUR Σ) :=
    λ (m : iResUR Σ) (i : gid Σ),
      map_imap (λ γ a,
        (* Apply the transformation in [trans], otherwise return unchanged. *)
          Some (from_option (λ t, map_unfold (t (map_fold a))) a (trans i !! γ))
      ) (m i).

  (* Build a global generational transformation based on the transformations in
   * [trans]. *)
  Definition trans_insert (i : gid Σ) (γ : gname) (t : R Σ i → R Σ i)
      (ts : iResUR Σ → iResUR Σ) : iResUR Σ → iResUR Σ :=
    λ (m : iResUR Σ) i',
      match decide (i = i') with
        left eq =>
          let t' : R Σ i' → R Σ i' := (rew [λ i, _] eq in t) in
          let n : gmap gname (Rpre Σ i') :=
            from_option (λ a, {[ γ := map_unfold (t' (map_fold a)) ]}) ∅ (m i' !! γ)
          in n ∪ ((ts m) i')
      | right _ => (ts m) i'
      end.

End nextgen_pointwise.

Section nextgen_inG.
  Context {Σ} `{i : inG Σ A}.
  Implicit Types (t : A → A) (ts : iResUR Σ → iResUR Σ).

  Definition trans_insert_inG γ t ts : iResUR Σ → iResUR Σ :=
    trans_insert (inG_id i) γ (cmra_map_transport inG_prf t) ts.

  (* Create a transformation that applies the transformation [t] to the ghost
   * location at the type [i] and the ghost name [γ]. *)
  Definition trans_single γ t : iResUR Σ → iResUR Σ := trans_insert_inG γ t id.

  #[global]
  Instance trans_single_cmra_morphism γ t :
    CmraMorphism t → CmraMorphism (trans_single γ t).
  Proof.
  Admitted.

  Lemma trans_single_own γ t `{!CmraMorphism t} a :
    own γ (a : A) ⊢ ⚡={trans_single γ t}=> own γ (t a).
  Proof.
    rewrite own.own_eq /own.own_def.
    iIntros "H".
    assert (CmraMorphism (trans_single γ t)). { apply _. }
    iModIntro.
    unfold trans_single, trans_insert_inG, trans_insert. simpl.
    iApply uPred.ownM_mono; last iApply "H".
    simpl.
    unfold own.iRes_singleton.
    apply discrete_fun_included_spec => id.
    destruct (decide (inG_id i = id)) as [<-|]; last first.
    { rewrite discrete_fun_lookup_singleton_ne; done. }
    rewrite 2!discrete_fun_lookup_singleton.
    rewrite lookup_singleton.
    apply singleton_included_l.
    simpl.
    eexists _.
    split.
    - erewrite lookup_union_Some_l; first reflexivity.
      rewrite lookup_singleton. reflexivity.
    - apply Some_included. left.
      rewrite -(map_unfold_inG_unfold _).
      f_equiv.
      rewrite -(map_unfold_inG_unfold _).
      rewrite map_fold_unfold.
      rewrite cmra_map_transport_cmra_transport.
      done.
  Qed.

  Lemma trans_single_own_other {B : cmra} γ t `{!CmraMorphism t}
      γ' (b : B) `{i' : inG Σ B} :
    A ≠ B →
    own γ' (b : B) ⊢ ⚡={trans_single γ t}=> own γ' b.
  Proof.
    intros neq.
    assert (inG_id i ≠ inG_id i') as neq2.
    { intros eq. apply neq.
      rewrite (inG_prf (inG := i)) (inG_prf (inG := i')).
      unfold inG_apply. congruence. }
    rewrite own.own_eq /own.own_def.
    iIntros "H".
    assert (CmraMorphism (trans_single γ t)). { apply _. }
    iModIntro.
    unfold trans_single, trans_insert_inG, trans_insert. simpl.
    iApply uPred.ownM_mono; last iApply "H".
    simpl.
    unfold own.iRes_singleton.
    apply discrete_fun_included_spec => id.
    destruct (decide (inG_id i = id)) as [<-|].
    { rewrite discrete_fun_lookup_singleton_ne; done. }
    done.
  Qed.

End nextgen_inG.
