From iris.proofmode Require Import classes tactics.
(* From iris.base_logic.lib Require Export iprop own invariants. *)
From iris.prelude Require Import options.

From nextgen.lib Require Import updates.
From nextgen Require Import cmra_morphism_extra.
From nextgen Require Export gen_trans nextgen_basic.
Import uPred.

(** When working in the model, it is convenient to be able to treat [uPred] as
[nat → M → Prop]. But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.

(** a basic update modality where updated result is not altered by a function t *)
(* Local Program Definition uPred_restr_bupd_def {M : ucmra} *)
(*   (t : M → M) `{!CmraMorphism t} (Q : uPred M) : uPred M := *)
(*   {| uPred_holds n x := ∀ k yf, *)
(*       k ≤ n → ✓{k} (x ⋅ yf) -> t x ≡ x -> ∃ x', ✓{k} (x' ⋅ yf) ∧ t x' ≡ x' /\ Q k x' *)
(*   |}. *)
(* Next Obligation. *)
(*   intros M t Htrans Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk. *)
(*   rewrite {1}(dist_le _ _ _ _ Hx); last lia. intros Hxy Heq. *)
(*   simpl in *. *)
(*   destruct (HQ k ((yf))) as (x'&?&?&?); [lia| |auto|]. *)
(*   { rewrite comm assoc in Hxy. apply cmra_validN_op_l in Hxy. *)
(*     rewrite comm. auto. } *)
(*   exists x'. repeat split;auto. *)
(* Qed. *)

(* Local Program Definition uPred_restr_bupd_def {M : ucmra} *)
(*   (t : M → M) `{!CmraMorphism t} (Q : uPred M) : uPred M := *)
(*   {| uPred_holds n x := ∀ k yf, *)
(*       k ≤ n → ✓{k} (t (x ⋅ yf)) -> ∃ x', ✓{k} (t x' ⋅ yf) /\ Q k (t x') *)
(*   |}. *)
(* Next Obligation. *)
(*   intros M t Htrans Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk. *)
(*   rewrite {1}(dist_le _ _ _ _ Hx); last lia. intros Hxy. *)
(*   simpl in *. *)
(*   destruct (HQ k (t x3 ⋅ yf)) as (x'&?&?); [lia|auto|]. *)
(*   { rewrite assoc -cmra_morphism_op. auto. } *)
(*   exists x'. repeat split;auto. *)
(*   rewrite assoc comm assoc in H. *)
(*   apply cmra_validN_op_l in H. *)
(*   by rewrite comm. *)
(* Qed. *)

(* Local Program Definition uPred_restr_bupd_def {M : ucmra} *)
(*   (t : M → M) `{!CmraMorphism t} (Q : uPred M) : uPred M := *)
(*   {| uPred_holds n x := ∀ k yf m, *)
(*       k ≤ n → ✓{k} (x ⋅ (Nat.iter m t yf)) -> ∃ x', ✓{k} (x' ⋅ (Nat.iter m t yf)) /\ t x' ≡ x' /\ Q k (x') *)
(*   |}. *)
(* Next Obligation. *)
(*   intros M t Htrans Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf m Hk. *)
(*   rewrite {1}(dist_le _ _ _ _ Hx); last lia. intros Hxy. *)
(*   simpl in *. *)
(*   destruct (HQ k ((* x3 ⋅  *)yf) m) as (x'&Hx'); [lia|auto|]. *)
(*   { rewrite comm assoc in Hxy. apply cmra_validN_op_l in Hxy. rewrite comm;auto. } *)
(*   exists x';auto. *)
(* Qed. *)

#[global] Instance iter_ne {M : ucmra} (f : M -> M) m : NonExpansive f -> NonExpansive (Nat.iter m f).
Proof.
  intros. intros m1 m2 HM.
  induction m;simpl;auto.
  apply H. auto.
Qed.

Lemma iter_op {M : ucmra} (f : M -> M) m :
  NonExpansive f ->
  (∀ x y : M, f (x ⋅ y) ≡ f x ⋅ f y) ->
  (∀ x y, (Nat.iter m f x) ⋅ (Nat.iter m f y) ≡ Nat.iter m f (x ⋅ y)).
Proof.
  intros Hne Hcond.
  induction m;simpl;auto.
  intros x y.
  rewrite -Hcond. 
  apply equiv_dist. intros k. apply Hne.
  revert k. apply equiv_dist. auto.
Qed.

Local Program Definition uPred_restr_bupd_def {M : ucmra}
  (t : M → M) `{!CmraMorphism t} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (t x ⋅ yf) -> ∃ x', ✓{k} (x' ⋅ yf) /\ t x' ≡{k}≡ x' /\ Q k x'
  |}.
Next Obligation.
  intros M t Htrans Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk.
  rewrite {1}(dist_le _ _ _ _ Hx); last lia. intros Hxy.
  simpl in *.
  
  destruct (HQ k (t x3 ⋅ yf)) as (x'&?&?&?); [lia|auto|].
  { rewrite assoc. rewrite cmra_morphism_op in Hxy. auto. }
  exists x'. repeat split;auto.
  rewrite assoc comm assoc in H.
  apply cmra_validN_op_l in H.
  by rewrite comm.
Qed.
  

Local Definition uPred_restr_bupd_aux : seal (@uPred_restr_bupd_def).
Proof. by eexists. Qed.

Definition uPred_restr_bupd {M : ucmra} f {g} :=
   uPred_restr_bupd_aux.(unseal) M f g.

Local Definition uPred_restr_bupd_unseal :
  @uPred_restr_bupd = @uPred_restr_bupd_def := uPred_restr_bupd_aux.(seal_eq).

Notation "|=/ f => P" := (uPred_restr_bupd f P)
                            (at level 99, f at level 50, P at level 200, format "|=/ f =>  P") : bi_scope.



Section restr_bupd_rules.
  Context {M : ucmra} (f : M → M) `{!CmraMorphism f}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; rewrite !uPred_restr_bupd_unseal !/uPred_holds /=.

  Lemma next_gen_bupd_commute P :
    (forall x, f x = f (f x)) ->
    (⚡={f}=> |=/f=> P) ⊢ |=/f=> ⚡={f}=> P.
  Proof.
    intros Hidemp. unseal. split. rewrite /uPred_bnextgen seal_eq /nextgen_basic.uPred_bnextgen_def.
    intros n x Hx Hcond.
    simpl in *.
    intros k yf Hkn Hv.
    rewrite Hidemp in Hv.
    apply Hcond in Hv as Hx';auto.
    destruct Hx' as [x' [Hvm [Heq Hx']]].
    exists x'. repeat split;auto. rewrite Heq//.
  Qed.

  Lemma bupd_ne : NonExpansive (@uPred_restr_bupd M f _).
  Proof.
    intros n P Q HPQ.
    unseal. split. intros. simpl in *.
    split =>HH k ? Hle B;pose proof (HH _ _ Hle B) as (?&?&?&?); eexists;eexists; repeat split;eauto.
    all: apply HPQ;auto;[lia|];eauto using cmra_validN_op_l.
  Qed.

  Lemma test P : (|=/f=> P) ⊢ |==> P.
  Proof.
    unseal. split;intros.
    simpl in *. intros.
    apply (cmra_morphism_validN f) in H2.
    rewrite cmra_morphism_op in H2.
    apply H0 in H2 as [x'[? [? ?]]];eauto.
  Abort.
    
    

  (* Lemma bupd_ownM_updateP x (Φ : M → Prop) : *)
  (*   x ~~>:{f} Φ → uPred_ownM x ⊢ |=/f=> ∃ y, ⌜Φ (f y)⌝ ∧ uPred_ownM (f y). *)
  (* Proof. *)
  (*   unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??. *)
  (*   destruct (Hup k (Some (f x3 ⋅ yf))) as (y&?&?); simpl in *. *)
  (*   { rewrite /= assoc -cmra_morphism_op -(dist_le _ _ _ _ Hx); auto. } *)
  (*   exists (y ⋅ x3); split; first by rewrite cmra_morphism_op -assoc. *)
  (*   exists y; split; eauto using cmra_morphism_op, cmra_includedN_l. *)
  (*   exists (f x3). rewrite cmra_morphism_op;auto. *)
  (* Qed. *)
  
  
  Lemma test P R : (forall x, f x = f (f x)) ->
                   (|=/f=> P) ∗ R ⊢ |=/f=> P ∗ R.
  Proof.
    intros Hidemp. unseal. split.
    intros n x Hx [x1 [x2 [Heq [Hop HR]]]].
    intros k yf Hk Hv.
    rewrite /uPred_restr_bupd_def in Hop.
    simpl in *. assert (✓{k} (f x ⋅ yf)) as Hv';auto.
    rewrite {1}(dist_le _ _ _ _ Heq) in Hv; last auto.
    rewrite cmra_morphism_op -assoc in Hv.
    apply Hop in Hv as Hx';auto.
    destruct Hx' as [x' [Hx' [Heq' HP]]].
    exists (x' ⋅ f x2). repeat split;auto.
    { by rewrite -assoc. }
    { rewrite cmra_morphism_op -Hidemp Heq'. auto. }
    exists x',x2.
  Abort.
    

(* (** Basic update modality *) *)
(*   Lemma bupd_intro P : P ⊢ |==> P. *)
(*   Proof. *)
(*     unseal. split=> n x ? HP k yf ?; exists x; split; first done. *)
(*     apply uPred_mono with n x; eauto using cmra_validN_op_l. *)
(*   Qed. *)
(*   Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q. *)
(*   Proof. *)
(*     unseal. intros HPQ; split=> n x ? HP k yf ??. *)
(*     destruct (HP k yf) as (x'&?&?); eauto. *)
(*     exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l. *)
(*   Qed. *)
(*   Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P. *)
(*   Proof. unseal; split; naive_solver. Qed. *)
(*   Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R. *)
(*   Proof. *)
(*     unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??. *)
(*     destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto. *)
(*     { by rewrite assoc -(dist_le _ _ _ _ Hx); last lia. } *)
(*     exists (x' ⋅ x2); split; first by rewrite -assoc. *)
(*     exists x', x2. eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r. *)
(*   Qed. *)
(*   Lemma bupd_plainly P : (|==> ■ P) ⊢ P. *)
(*   Proof. *)
(*     unseal; split => n x Hnx /= Hng. *)
(*     destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto. *)
(*     eapply uPred_mono; eauto using ucmra_unit_leastN. *)
(*   Qed. *)

  
End restr_bupd_rules.

