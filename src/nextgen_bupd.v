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


Class GenTransExtra {A : cmra} (f : A -> A) := {
    gen_trans_op_inv n a :
    (∀ b1 b2, f a ≡{n}≡ b1 ⋅ b2 →
              ∃ a1 a2, a ≡{n}≡ a1 ⋅ a2 ∧ f a1 ≡{n}≡ b1 ∧ f a2 ≡{n}≡ b2)
}.

Local Program Definition uPred_restr_bupd_def {M : ucmra}
  (t : M → M) `{!CmraMorphism t} `{!GenTransExtra t} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n -> ✓{k} (x ⋅ yf) -> ∃ x' x1' x2', x' ≡{k}≡ x1' ⋅ x2' /\ x1' ≡{k}≡ t x1'
          /\ (∃ x2, x ≡{k}≡ x2 ⋅ x2' /\ (∀ x3 x2'' yf', x2 ≡{k}≡ t x3 -> x2' ≡{k}≡ t x2'' -> yf ≡{k}≡ t yf' ->
                                                                                        ✓{k} (x3 ⋅ x2'' ⋅ yf') -> ✓{k} (x1' ⋅ x2'' ⋅ yf')))
                                            /\ ✓{k} (x' ⋅ yf)
                                            /\ Q k x' |}.
Next Obligation.
  intros M t Htrans Htransextra Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk (* [x1' [x2' [Heq1 Ht]]] *).
  rewrite {1}(dist_le _ _ _ _ Hx); last lia. intros Hxy.
  simpl in *.
  destruct (HQ k (x3 ⋅ yf)) as (x'&x1'&x2'&Heq'&Heq2&(x2''&Hx2'&Himpl)&Hv&HQ'); [lia|auto|..].
  { by rewrite assoc. (* rewrite -assoc (comm _ x3 yf) assoc in Hxy. apply cmra_validN_op_l in Hxy; auto.  *)}
  exists (x' ⋅ x3),x1',(x2' ⋅ x3). rewrite (assoc op) -Heq'.
  split;[|split];auto. rewrite assoc in Hv. split;[|split];auto.
  - exists (x2'').
    rewrite (dist_le _ _ _ _ Hx); last lia. rewrite assoc Hx2' //.
    split;auto.
    intros x0 x2''0 yf' HH Heqx2'' Heqyf.
    symmetry in Heqx2''.
    apply gen_trans_op_inv in Heqx2'' as Ha.
    destruct Ha as [a1 [a2 [Ha12 [Ha1 Ha2]]]].
    symmetry in Ha1. intros Hx0.
    apply (Himpl _ _ (a2 ⋅ yf') HH) in Ha1 as Hii;[|rewrite cmra_morphism_op Ha2 -Heqyf//|].
    + rewrite Ha12. rewrite assoc in Hii. rewrite assoc. auto.
    + rewrite assoc. rewrite -(assoc _ _ a1 a2). rewrite -Ha12. auto.
  - eapply uPred_mono;eauto. by exists x3.
Qed.


Local Definition uPred_restr_bupd_aux : seal (@uPred_restr_bupd_def).
Proof. by eexists. Qed.

Definition uPred_restr_bupd {M : ucmra} f {g} {g'} :=
   uPred_restr_bupd_aux.(unseal) M f g g'.

Local Definition uPred_restr_bupd_unseal :
  @uPred_restr_bupd = @uPred_restr_bupd_def := uPred_restr_bupd_aux.(seal_eq).

Notation "|=/ f => P" := (uPred_restr_bupd f P)
                            (at level 99, f at level 50, P at level 200, format "|=/ f =>  P") : bi_scope.



Section restr_bupd_rules.
  Context {M : ucmra} (f : M → M) `{!CmraMorphism f} `{!GenTransExtra f}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; rewrite !uPred_restr_bupd_unseal !/uPred_holds /=.

  Lemma nextgen_restr_bupd_commute P :
    (forall x, f x = f (f x)) ->
    (⚡={f}=> |=/f=> P) ⊢ |=/f=> ⚡={f}=> P.
  Proof.
    intros Hidemp. unseal. split. rewrite /uPred_bnextgen seal_eq /nextgen_basic.uPred_bnextgen_def.
    intros n x Hx Hcond.
    simpl in *.
    intros k yf Hkn Hv.
    assert (✓{k} (x ⋅ yf)) as Hv_copy;auto.
    apply (cmra_morphism_validN f) in Hv.
    rewrite cmra_morphism_op in Hv.
    apply Hcond in Hv as Hx';auto.
    destruct Hx' as (x'&x1'&x2'&Heq1&Heq2&(x2&Hfeq&Himpl)&Hv'&HP).
    apply gen_trans_op_inv in Hfeq as Ha.
    destruct Ha as [a1 [a2 [Ha12 [Ha1 Ha2]]]].
    exists (x1' ⋅ a2). eexists. eexists.
    symmetry in Ha1. symmetry in Ha2.
    eapply Himpl in Ha1 as HH;eauto;cycle 1.
    { rewrite -Ha12. auto. }
    
    repeat split;eauto.
    { exists a1. split;auto. intros. rewrite H0 in Ha2. rewrite -Hidemp in Ha2.
      rewrite H in Ha1. rewrite -Hidemp in Ha1. eapply Himpl in Ha2;eauto.
      rewrite H1. rewrite -Hidemp. auto.
    }
    { rewrite cmra_morphism_op -Ha2 -Heq2 -Heq1. auto. }
  Qed.

  Lemma restr_bupd_ne : NonExpansive (@uPred_restr_bupd M f _ _).
  Proof.
    intros n P Q HPQ.
    unseal. split. intros. simpl in *.
    split =>HH k ? Hle B;pose proof (HH _ _ Hle B) as (?&?&?&?&?&(?&?&?)&?&?); do 3 eexists;(split;[apply H1|..]);repeat (split;eauto).
    all: (apply HPQ;auto;[lia|..]; eauto using cmra_validN_op_l).
  Qed.

  Lemma restr_bupd_bupd P : (|=/f=> P) ⊢ |==> P.
  Proof.
    unseal. split;intros ??? Hcond.
    simpl in *. intros k yf Hle Hv.
    apply Hcond in Hv as (?&?&?&?&?&(?&?&?)&?&?);eauto.
  Qed.

  Lemma restr_bupd_frame_r P R : (|=/f=> P) ∗ R ⊢ |=/f=> P ∗ R.
  Proof.
    unseal. split.
    intros n x Hx [x1 [x2 [Heq [Hop HR]]]].
    intros k yf Hk. rewrite {1}(dist_le _ _ _ _ Heq); last lia. intros Hv. simpl in *.
    edestruct (Hop k (x2 ⋅ yf)) as [x' [x1' [x2' [Heq1 [Heq2 [[x3 [Hx3 Hcond2]] [Hv' HP']]]]]]];auto.
    { by rewrite assoc. (* rewrite -assoc (comm _ x2 yf) assoc in Hv. by apply cmra_validN_op_l in Hv.  *)}
    (* rewrite assoc in Hx'. *)
    exists (x' ⋅ x2),(x1'),(x2' ⋅ x2).
    repeat split;eauto.
    - rewrite Heq1 assoc. auto.
    - exists (x3). rewrite assoc -Hx3. rewrite (dist_le _ _ _ _ Heq);auto.
      split;auto.
      intros x0 x2'' yf' Heq0 Heqf Hyf'.
      symmetry in Heqf.
      apply gen_trans_op_inv in Heqf as Ha.
      destruct Ha as [a1 [a2 [Ha12 [Ha1 Ha2]]]].
      symmetry in Ha1. intros Hvv.
      eapply Hcond2 in Ha1 as Ha1';cycle 1.
      { apply Heq0. }
      { instantiate (1:=a2 ⋅ yf'). rewrite cmra_morphism_op -Ha2 -Hyf'. auto. }
      { rewrite assoc -(assoc _ _ a1 a2) -Ha12//. }
      rewrite Ha12. rewrite assoc in Ha1'. rewrite assoc. auto.
    - by rewrite -assoc.
    - exists x', x2. repeat split; auto.
      eapply uPred_mono;eauto.
  Qed.

  (* Definition cmra_updateP {A : cmra} (t : A → A) `{!CmraMorphism t} (x : A) (P : A → Prop) := ∀ n (mz : option A), *)
  (*     ✓{n} (x ⋅? mz) /\ t x1 ≡ x1 /\ x ≡ x1 ⋅ x2 -> ∃ x1 y y1, P (y) /\ ✓{n} (y ⋅? mz) /\ t y1 ≡ y1 /\ y ≡ y1 ⋅ x2. *)
  (* Global Instance: Params (@cmra_updateP) 1 := {}. *)
  (* Global Instance: Params (@cmra_updateP) 3 := {}. *)
  (* Infix "~~>:{  t  }" := (cmra_updateP t) (at level 70). *)

  (* Lemma bupd_ownM_updateP x (Φ : M → Prop) : *)
  (*   x ~~>:{f} Φ → uPred_ownM x ⊢ |=/f=> ∃ y, ⌜Φ (f y)⌝ ∧ uPred_ownM (f y). *)
  (* Proof. *)
  (*   unseal=> Hup; split=> n x2 Hv1 [x3 Hx] k yf Hle Hv2. *)
  (*   destruct (Hup k (Some (x3 ⋅ yf)) ) as (y&?&?); simpl in *. *)
  (*   { rewrite /= assoc -cmra_morphism_op -(dist_le _ _ _ _ Hx); auto. } *)
  (*   exists (y ⋅ x3); split; first by rewrite cmra_morphism_op -assoc. *)
  (*   exists y; split; eauto using cmra_morphism_op, cmra_includedN_l. *)
  (*   exists (f x3). rewrite cmra_morphism_op;auto. *)
  (* Qed. *)

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

