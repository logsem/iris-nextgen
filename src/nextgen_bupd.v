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
(*       k ≤ n → ✓{k} (x ⋅ yf) -> t yf ≡ yf -> ∃ x', ✓{k} (x' ⋅ yf) ∧ t x' ≡ x' /\ Q k x' *)
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
Local Program Definition uPred_restr_bupd_def {M : ucmra}
  (t : M → M) `{!CmraMorphism t} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (t x ⋅ yf) -> ∃ x', ✓{k} (t x' ⋅ yf) /\ Q k (t x')
  |}.
Next Obligation.
  intros M t Htrans Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk.
  rewrite {1}(dist_le _ _ _ _ Hx); last lia. intros Hxy.
  simpl in *.
  
  destruct (HQ k (t x3 ⋅ yf)) as (x'&?&?); [lia|auto|].
  { rewrite assoc -cmra_morphism_op. auto. }
  exists x'. repeat split;auto.
  rewrite assoc comm assoc in H.
  apply cmra_validN_op_l in H.
  by rewrite comm.
Qed.
  
(*   destruct (HQ k ((x3 ⋅ yf))) as (x'&?&?&?&?); [lia|by rewrite assoc|]. *)
(*   exists (x'). repeat split;auto. *)
(*   { rewrite comm -assoc in H. *)
(*     apply cmra_validN_op_r in H. *)
(*     rewrite comm;auto. } *)
(*   { intros. rewrite H3 in H2. specialize H2 with (x3 ⋅ yf'). apply H2 in H3. } *)
(* Qed. *)
(*   (* { rewrite cmra_morphism_op in H. *) *)
(*   (*   rewrite comm -assoc in H. *) *)
(*   (*   apply cmra_validN_op_r in H. *) *)
(*   (*   rewrite comm. auto. } *) *)
(*   { rewrite comm -assoc in H. *)
(*     apply cmra_validN_op_r in H. *)
(*     rewrite comm. auto.  } *)
(*   (* { intros. *) *)
(*   (*   admit. *) *)
(*   (* } *) *)
(* Qed. *)


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

  Lemma test P :
    (forall x, f x = f (f x)) ->
    (⚡={f}=> |=/f=> P) ⊢ |=/f=> ⚡={f}=> P.
  Proof.
    intros Hidemp. unseal. rewrite /uPred_bnextgen seal_eq /nextgen_basic.uPred_bnextgen_def.
    split. intros.
    simpl in *.
    intros k yf Hkn Hv.
    rewrite Hidemp in Hv.
    apply H0 in Hv as Hx';auto.
    destruct Hx' as [x' [Hx' HP] ].
    exists x'. rewrite -Hidemp. auto.
  Qed.

  Lemma bupd_ne : NonExpansive (@uPred_restr_bupd M f _).
  Proof.
    intros n P Q HPQ.
    unseal. split. intros. simpl in *.
    split =>HH k ? Hle B;pose proof (HH _ _ Hle B) as (?&?&?); eexists;repeat split;eauto.
    all: apply HPQ;auto;[lia|];eauto using cmra_validN_op_l.
  Qed.

  Lemma bupd_ownM_updateP x (Φ : M → Prop) :
    x ~~>:{f} Φ → uPred_ownM x ⊢ |=/f=> ∃ y, ⌜Φ (f y)⌝ ∧ uPred_ownM (f y).
  Proof.
    unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??.
    destruct (Hup k (Some (f x3 ⋅ yf))) as (y&?&?); simpl in *.
    { rewrite /= assoc -cmra_morphism_op -(dist_le _ _ _ _ Hx); auto. }
    exists (y ⋅ x3); split; first by rewrite cmra_morphism_op -assoc.
    exists y; split; eauto using cmra_morphism_op, cmra_includedN_l.
    exists (f x3). rewrite cmra_morphism_op;auto.
  Qed.
  

  
    
End restr_bupd_rules.

