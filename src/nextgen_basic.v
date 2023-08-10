(* The basic nextgen modality. *)

From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants fancy_updates.
From iris.prelude Require Import options.

From nextgen Require Import cmra_morphism_extra.
From nextgen Require Export gen_trans.
Import uPred.

(** When working in the model, it is convenient to be able to treat [uPred] as
[nat → M → Prop]. But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.

(* The _basic_ next-gen modality. *)
Local Program Definition uPred_bnextgen_def {M : ucmra}
  (t : M → M) `{!GenTrans t} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (t x) |}.
Next Obligation.
  intros ????? n.
  specialize (gen_trans_monoN t n) as monoN.
  naive_solver eauto using uPred_mono, monoN.
Qed.

Local Definition uPred_bnextgen_aux : seal (@uPred_bnextgen_def).
Proof. by eexists. Qed.

Definition uPred_bnextgen {M : ucmra} f {g} :=
  uPred_bnextgen_aux.(unseal) M f g.

Local Definition uPred_bnextgen_unseal :
  @uPred_bnextgen = @uPred_bnextgen_def := uPred_bnextgen_aux.(seal_eq).

Notation "⚡={ f }=> P" := (uPred_bnextgen f P)
  (at level 99, f at level 50, P at level 200, format "⚡={ f }=>  P") : bi_scope.

Class IntoBnextgen `{M : ucmra}
    f `{!GenTrans f}
    (P : uPred M) (Q : uPred M) :=
  into_bnextgen : P ⊢ ⚡={ f }=> Q.
Global Arguments IntoBnextgen  {_} _%I {_} _%I _%I.
Global Arguments into_bnextgen {_} _%I _%I {_}.
Global Hint Mode IntoBnextgen + + + ! - : typeclass_instances.

Section bnextgen_rules.
  Context {M : ucmra} (f : M → M) `{!GenTrans f}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; rewrite !uPred_bnextgen_unseal !/uPred_holds /=.

  Lemma bnextgen_ownM (a : M) :
    uPred_ownM a ⊢ ⚡={f}=> uPred_ownM (f a).
  Proof.
    unseal. split. simpl. intros n x Hv ?. apply: gen_trans_monoN. done.
  Qed.

  Lemma bnextgen_ownM_inv' (a : M) b :
    (∀ x n, b ≼{n} f x → a ≼{n} x) →
    (⚡={f}=> uPred_ownM b) ⊢ uPred_ownM a.
  Proof. intros H. unseal. split. simpl. intros n x Hv ?. apply H. done. Qed.

  (* If the transformation is contractive, ie. _only_ removes things, then
   * we can eliminate it. *)
  Lemma bnextgen_elim_contractive P :
    (∀ x n, f x ≼{n} x) →
    (⚡={f}=> P) ⊢ P.
  Proof.
    intros ?. unseal. split. simpl. intros. eapply uPred_mono; done.
  Qed.

  Lemma bnextgen_idemp P :
    (∀ x, f x = f (f x)) →
    (⚡={f}=> P) ⊣⊢ (⚡={f}=> ⚡={f}=>P).
  Proof.
    intros ?. unseal. split. simpl. intros.
    rewrite {1}H;auto. 
  Qed.
  
  (* If we own an element [a], we have a lower bound on elements for which we
   * have to show that [f] is contractive. *)
  Lemma bnextgen_elim_ownM_contractive (a : M) P :
    (∀ x n, a ≼{n} x → f x ≼{n} x) →
    uPred_ownM a ∧ (⚡={f}=> P) ⊢ uPred_ownM a ∧ P.
  Proof.
    intros incl. unseal. split. simpl. intros ??? [??].
    split; first done. eapply uPred_mono; eauto.
  Qed.

  Lemma bnextgen_elim_ownM_fupd_contractive (a : M) P :
    (∀ x yf k, (* This condition is probably too strong. *)
      ✓{k} (x ⋅ yf) →
      a ≼{k} f x →
      ✓{k} (f x ⋅ yf)) →
    uPred_ownM a ∧ (|==> ⚡={f}=> uPred_ownM a ∧ P) ⊢
    uPred_ownM a ∧ |==> P.
  Proof.
    intros cond. unseal. split. simpl. intros ? initX ? [xLb updNgOwn].
    split; first done.
    intros.
    destruct (updNgOwn _ _ H0 H1) as (xUpd & ? & ? & ?).
    eexists _. split; last done.
    apply cond; done.
  Qed.

  Lemma bnextgen_elim_ownM_2 (a b c : M) :
    (∀ x n, a ≼{n} x → b ≼{n} f x → c ≼{n} x) →
    uPred_ownM a ∧ (⚡={f}=> uPred_ownM b) ⊢
    uPred_ownM c.
  Proof.
    intros incl. unseal. split. simpl. intros ??? [??]. apply incl; done.
  Qed.

  Lemma bnextgen_elim_ownM_inv (a : M) g
      `{mono : ∀ n, Proper (includedN n ==> includedN n) g} :
    (∀ a, g (f a) = a) →
    (⚡={f}=> uPred_ownM a) ⊢ uPred_ownM (g a).
  Proof.
    intros eq. apply bnextgen_ownM_inv'.
    intros ?? incl%mono. rewrite eq in incl. done.
  Qed.

  #[global] Instance bnextgen_ne : NonExpansive (uPred_bnextgen f).
  Proof.
    unseal. intros ? P Q Heq.
    split. intros ????. simpl.
    apply Heq; first done.
    apply: gen_trans_validN. done.
  Qed.

  Lemma bnextgen_and P Q :
    (⚡={f}=> P) ∧ (⚡={f}=> Q) ⊣⊢ ⚡={f}=> (P ∧ Q).
  Proof. unseal. split. simpl. done. Qed.

  Lemma bnextgen_or P Q :
    (⚡={f}=> P) ∨ (⚡={f}=> Q) ⊣⊢ ⚡={f}=> (P ∨ Q).
  Proof. unseal. split. simpl. done. Qed.

  Notation "□ P" := (uPred_persistently P) : bi_scope.

  (* Unlike [bnextgen_sep_2] this lemma does not depend on [CmraMorphism].
   * Instead it relies on properties that are true for the core. TODO: Find the
   * most general version of this lemma. *)
  Lemma bnextgen_sep_2_alt P Q :
    (∀ a, f a ≡ f a ⋅ f a) →
    (∀ a b n, a ≼{n} b → f a ≼{n} f b) →
    (⚡={f}=> P) ∗ (⚡={f}=> Q) ⊢ ⚡={f}=> (P ∗ Q) .
  Proof.
    intros Hdup Hmono.
    unseal.
    split=> n x ?. intros (x1 & x2 & eq & ? & ?). simpl.
    exists (f (x1 ⋅ x2)), (f (x1 ⋅ x2)). simpl in *.
    split_and!.
    - rewrite eq. rewrite -Hdup. done.
    - eapply uPred_mono; first done; last done.
      apply Hmono. apply cmra_includedN_l.
    - eapply uPred_mono; first done; last done.
      apply Hmono. apply cmra_includedN_r.
  Qed.

  Lemma bnextgen_intro_plainly P :
    ■ P ⊢ ⚡={f}=> ■ P.
  Proof. unseal. split. done. Qed.

  Lemma bnextgen_plainly P :
    (⚡={f}=> ■ P) ⊢ P.
  Proof.
    unseal. split. simpl. intros ????. simpl.
    eauto using uPred_mono, ucmra_unit_leastN.
  Qed.

  Lemma bnextgen_wand_plainly P Q :
    (⚡={f}=> (■ P -∗ Q)) ⊣⊢ (■ P -∗ ⚡={f}=> Q).
  Proof.
    unseal. split. simpl. intros ???.
    split.
    * intros Hi n' x' le val Hp.
      specialize (Hi n' ε le).
      rewrite right_id in Hi.
      eapply uPred_mono.
      - apply Hi.
        + eapply cmra_validN_le; last done.
          apply: gen_trans_validN.
          done.
        + done.
      - apply: gen_trans_monoN. eexists _. done.
      - done.
    * intros Hi n' x' le val Hp.
      specialize (Hi n' ε le).
      rewrite right_id in Hi.
      eapply uPred_mono.
      - apply Hi.
        + eapply cmra_validN_le; try done.
        + done.
      - eexists _. done.
      - done.
  Qed.

  Lemma bnextgen_mono P Q :
    (P ⊢ Q) → (⚡={f}=> P) ⊢ ⚡={f}=> Q.
  Proof.
    intros [Hi].
    unseal. split. simpl.
    intros ???.
    apply Hi.
    apply: gen_trans_validN.
    done.
  Qed.

  Lemma bnextgen_idemp_mono P Q :
    (forall x, f x = f (f x)) →
    (P ⊢ ⚡={f}=> Q) -> (⚡={f}=> P) ⊢ ⚡={f}=> Q.
  Proof.
    intros ??.
    rewrite {1}(bnextgen_idemp Q)//.
    apply bnextgen_mono=>//.
  Qed.

  Lemma bnextgen_idemp_mono_2 P Q :
    (forall x, f x = f (f x)) →
    ((⚡={f}=> P) ⊢ Q) -> (⚡={f}=> P) ⊢ ⚡={f}=> Q.
  Proof.
    intros ??.
    rewrite {1}(bnextgen_idemp P)//.
    apply bnextgen_mono=>//.
  Qed.

  Lemma bnextgen_emp_2 : emp ⊢ ⚡={f}=> emp.
  Proof. unseal. done. Qed.

  Global Instance bnextgen_mono' :
    Proper ((⊢) ==> (⊢)) (uPred_bnextgen f).
  Proof. intros P Q. apply bnextgen_mono. Qed.

  Global Instance bnextgen_proper :
    Proper ((≡) ==> (≡)) (uPred_bnextgen f) := ne_proper _.

  Lemma bnextgen_later P :
    ▷ (⚡={f}=> P) ⊣⊢ ⚡={f}=> (▷ P).
  Proof. unseal. done. Qed.

  Lemma bnextgen_laterN n P : (▷^n ⚡={f}=> P) ⊣⊢ ⚡={f}=> ▷^n P.
  Proof.
    induction n as [|n IH]; simpl; auto. rewrite IH bnextgen_later. done.
  Qed.

  Lemma bnextgen_exist {A} Ψ :
    (⚡={f}=> (∃ a : A, Ψ a)) ⊣⊢ (∃ a : A, ⚡={f}=> Ψ a).
  Proof. unseal. done. Qed.

  Lemma bnextgen_forall {A} Ψ :
    (⚡={f}=> (∀ a : A, Ψ a)) ⊣⊢ (∀ a : A, ⚡={f}=> Ψ a).
  Proof. unseal. done. Qed.

  Lemma bnextgen_intro_plain P `{!Plain P, !Absorbing P} :
    P ⊢ ⚡={f}=> P.
  Proof.
    rewrite -(plain_plainly P).
    apply bnextgen_intro_plainly.
  Qed.

  Lemma bnextgen_plain P `{!Plain P} :
    (⚡={f}=> P) ⊢ P.
  Proof. rewrite {1}(plain P). apply bnextgen_plainly. Qed.

  Global Instance into_later_bnextgen n P Q :
    IntoLaterN false n P Q →
    IntoLaterN false n (⚡={f}=> P) (⚡={f}=> Q).
  Proof.
    rewrite /IntoLaterN /MaybeIntoLaterN=> ->.
    rewrite bnextgen_laterN. done.
  Qed.

  (* Lemma bnextgen_wand_r P Q : *)
  (*   (⚡={f}=> P) ∗ (P -∗ Q) ⊢ ⚡={f}=> Q. *)
  (* Proof. *)
  (*   iIntros "[HP HI]". *)
  (*   (* iApply bnextgen_mono. *) *)
  (*   iApply (bnextgen_mono with "HP"). *)
  (*   unseal. split. simpl. *)
  (* Qed. *)

End bnextgen_rules.

Section bnextgen_compose_rules.
  Context {M : ucmra} (f : M → M) (g : M → M) `{!GenTrans f} `{!GenTrans g}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; rewrite !uPred_bnextgen_unseal !/uPred_holds /=.

  Local Instance compose_gentrans : GenTrans (g ∘ f).
  Proof using GenTrans0 GenTrans1.
    destruct GenTrans0, GenTrans1.
    split.
    - intros n x y Hxy.
      apply gen_trans_ne in Hxy.
      apply gen_trans_ne0 in Hxy.
      auto.
    - intros n x Hv.
      apply gen_trans_validN in Hv.
      apply gen_trans_validN0 in Hv. auto.
    - intros n x y Hincl.
      apply gen_trans_monoN in Hincl.
      apply gen_trans_monoN0 in Hincl.
      auto.
  Qed.
    
  Lemma bnextgen_compose P :
    (⚡={f}=> ⚡={g}=> P) ⊣⊢ ⚡={g ∘ f}=> P.
  Proof.
    split. unseal. intros. split;auto.
  Qed.

  Lemma bnextgen_compose_elim P :
    (forall x, g (f x) = g x) ->
    (⚡={g}=> P) ⊣⊢ ⚡={f}=> ⚡={g}=> P.
  Proof.
    intros ?. split. unseal. intros.
    rewrite H. auto.
  Qed.

  Lemma bnextgen_extensional_eq P :
    (forall x, f x = g x) ->
    (⚡={f}=> P) ⊣⊢ ⚡={g}=> P.
  Proof.
    intros Hext.
    split. unseal. intros.
    rewrite Hext. auto.
  Qed.

End bnextgen_compose_rules.

Section bnextgen_rules_cmra_morphism.
  Context {M : ucmra} (f : M → M) `{!CmraMorphism f}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; rewrite !uPred_bnextgen_unseal !/uPred_holds /=.

  Lemma bnextgen_wand_1 P Q :
    (⚡={f}=> P -∗ Q) ⊢ ((⚡={f}=> P) -∗ (⚡={f}=> Q)).
  Proof.
    unseal. split. intros ?? Hx Hi.
    simpl in *. intros.  apply Hi in H1;auto.
    - rewrite cmra_morphism_op//.
    - rewrite -cmra_morphism_op. apply cmra_morphism_validN =>//.
  Qed.
    

  Lemma bnextgen_sep_2 P Q :
    (⚡={f}=> P) ∗ (⚡={f}=> Q) ⊢ ⚡={f}=> (P ∗ Q) .
  Proof.
    unseal. split. simpl.
    intros ???.
    intros (a & b & eq & Hp & Hq).
    exists (f a), (f b).
    rewrite -(cmra_morphism_op _ a b).
    rewrite eq. done.
  Qed.

  Lemma bnextgen_sep P Q :
    (∀ n a b1 b2,
       f a ≡{n}≡ b1 ⋅ b2 →
       ∃ a1 a2, a ≡{n}≡ a1 ⋅ a2 ∧ f a1 ≡{n}≡ b1 ∧ f a2 ≡{n}≡ b2) →
    (⚡={f}=> P) ∗ (⚡={f}=> Q) ⊣⊢ ⚡={f}=> (P ∗ Q) .
  Proof.
    intros cond.
    apply (anti_symm _); first apply bnextgen_sep_2.
    unseal. split. simpl.
    intros ? a ?.
    intros (b1 & b2 & eq & Hp & Hq).
    destruct (cond n a b1 b2) as (a1 & a2 & ? & ? & ?); first done.
    exists a1, a2.
    subst.
    split; first done.
    rewrite H1.
    rewrite H2.
    split; done.
  Qed.

  Lemma bnextgen_intuitionistically P :
    (⚡={f}=> (<pers> P)) ⊣⊢ <pers> (⚡={f}=> P).
  Proof.
    unseal. split. simpl. intros ???.
    pose proof (cmra_morphism_pcore f x) as eq.
    rewrite 2!cmra_pcore_core in eq.
    apply Some_equiv_inj in eq.
    rewrite eq.
    done.
  Qed.

  Lemma bnextgen_intuitionistically_1 P :
    (⚡={f}=> (<pers> P)) ⊢ <pers> (⚡={f}=> P).
  Proof. rewrite bnextgen_intuitionistically. done. Qed.

  Lemma bnextgen_intuitionistically_2 P :
    <pers> (⚡={f}=> P) ⊢ ⚡={f}=> (<pers> P).
  Proof. rewrite bnextgen_intuitionistically. done. Qed.

  Lemma modality_bnextgen_mixin :
    modality_mixin (@uPred_bnextgen M f _)
      (MIEnvTransform (IntoBnextgen f)) (MIEnvTransform (IntoBnextgen f)).
  Proof.
    split; simpl; split_and?.
    - intros ?? Hi.
      rewrite Hi.
      rewrite 2!intuitionistically_into_persistently.
      apply bnextgen_intuitionistically_2.
    - intros. rewrite bnextgen_and. done.
    - done.
    - apply bnextgen_emp_2.
    - apply bnextgen_mono.
    - apply bnextgen_sep_2.
  Qed.
  Definition modality_bnextgen :=
    Modality _ modality_bnextgen_mixin.

  Global Instance from_modal_bnextgen P :
    FromModal True modality_bnextgen (⚡={f}=> P) (⚡={f}=> P) P | 1.
  Proof. by rewrite /FromModal. Qed.

End bnextgen_rules_cmra_morphism.

Lemma bnextgen_plain_soundness {M : ucmra} f `{!GenTrans f} (P : uPred M) `{!Plain P} :
  (⊢ ⚡={f}=> P) → ⊢ P.
Proof.
  eapply bi_emp_valid_mono. etrans; last exact: bnextgen_plainly.
  apply bnextgen_mono'. apply: plain.
Qed.

Section into_bnextgen.
  Context {M : ucmra} (f : M → M) `{!CmraMorphism f}.

  Global Instance into_bnextgen_ownM a :
    IntoBnextgen f (uPred_ownM a) (uPred_ownM (f a)) := bnextgen_ownM f a.

  Global Instance into_bnextgen_bnextgen P :
    IntoBnextgen f (⚡={f}=> P) P.
  Proof. done. Qed.

  Global Instance into_bnextgen_plain P `{!Plain P, !Absorbing P} :
    IntoBnextgen f P P.
  Proof. apply bnextgen_intro_plain; apply _. Qed.

  Global Instance into_bnextgen_and P P' Q Q' :
    IntoBnextgen f P P' →
    IntoBnextgen f Q Q' →
    IntoBnextgen f (P ∧ Q) (P' ∧ Q').
  Proof.
    rewrite /IntoBnextgen.
    intros -> ->.
    rewrite -bnextgen_and.
    done.
  Qed.

  Global Instance into_bnextgen_sep P P' Q Q' :
    IntoBnextgen f P P' →
    IntoBnextgen f Q Q' →
    IntoBnextgen f (P ∗ Q) (P' ∗ Q').
  Proof.
    rewrite /IntoBnextgen.
    iIntros (Hi1 Hi2) "[P Q]".
    rewrite Hi1 Hi2.
    iModIntro.
    iFrame.
  Qed.

  Global Instance into_bnextgen_later P P' :
    IntoBnextgen f P P' → IntoBnextgen f (▷ P) (▷ P').
  Proof. rewrite /IntoBnextgen. rewrite -bnextgen_later. intros ->. done. Qed.

  Global Instance into_bnextgen_forall {A} (Ψ Ψ' : A → _) :
    (∀ x, IntoBnextgen f (Ψ x) (Ψ' x)) → IntoBnextgen f (∀ x, Ψ x) (∀ x, Ψ' x).
  Proof.
    rewrite /IntoBnextgen bnextgen_forall.
    iIntros (H) "Hi". iIntros (?).
    iApply H.
    iApply "Hi".
  Qed.

  Global Instance into_bnextgen_exist {A} (Ψ Ψ' : A → _) :
    (∀ x : A, IntoBnextgen f (Ψ x) (Ψ' x)) → IntoBnextgen f (∃ x : A, Ψ x) (∃ x : A, Ψ' x).
  Proof.
    rewrite /IntoBnextgen bnextgen_exist.
    iIntros (H). iIntros "(%x & Hi)". iExists x.
    iApply H.
    iApply "Hi".
  Qed.

  Global Instance into_bnextgen_wand_plain P `{!Plain P} Q Q' :
      IntoBnextgen f Q Q' → IntoBnextgen f (P -∗ Q) (P -∗ Q').
  Proof.
    rewrite /IntoBnextgen.
    rewrite -(plain_plainly P).
    iIntros (H) "I".
    iApply bnextgen_wand_plainly.
    rewrite H.
    done.
  Qed.

  Global Instance into_bnextgen_impl_plain P `{!Plain P, !Persistent P} Q Q' :
      IntoBnextgen f Q Q' → IntoBnextgen f (P → Q) (P → Q').
  Proof.
    rewrite /IntoBnextgen.
    rewrite -(plain_plainly P).
    iIntros (H) "I".
    rewrite 2!impl_wand.
    iApply bnextgen_wand_plainly.
    rewrite H.
    done.
  Qed.

  Lemma bnextgen_wand_plain P `{!Plain P, !Absorbing P} Q :
    (⚡={f}=> (P -∗ Q)) ⊢ P -∗ ⚡={f}=> Q.
  Proof.
    iIntros "H P".
    iDestruct (bnextgen_intro_plain f P with "P") as "P".
    iModIntro.
    iApply "H". iApply "P".
  Qed.

  (* Lemma bnextgen_wand_plain_2 P `{!Plain P, !Absorbing P} Q : *)
  (*   (P -∗ ⚡={f}=> Q) ⊢ *)
  (*   ⚡={f}=> (P -∗ Q). *)
  (* Proof. *)
  (*   iIntros "H P". *)
  (*   iDestruct (bnextgen_intro_plain f P with "P") as "P". *)
  (*   iModIntro. *)
  (*   iApply "H". iApply "P". *)
  (* Qed. *)

  Lemma bnextgen_persistently_2 P :
    □ (⚡={f}=> P) ⊢ ⚡={f}=> (□ P).
  Proof.
    rewrite /bi_intuitionistically /bi_affinely.
    rewrite 2!left_id.
    rewrite bnextgen_intuitionistically.
    done.
  Qed.

  Global Instance bnextgen_persistent P :
    Persistent P → (Persistent (⚡={f}=> P)).
  Proof.
    rewrite /Persistent.
    intros ?.
    rewrite -bnextgen_intuitionistically.
    iIntros "H".
    iModIntro.
    iApply H.
    done.
  Qed.

  (* Lemma bnextgen_wand_plain' P `{!Plain P, !Absorbing P} Q : *)
  (*   (P -∗ Q) ⊢ ⚡={f}=> (P -∗ Q). *)
  (* Proof. *)
  (*   iIntros "H P". *)
  (*   iDestruct (bnextgen_intro_plain f P with "P") as "P". *)
  (*   iModIntro. *)
  (*   iApply "H". iApply "P". *)
  (* Qed. *)

  Lemma bnextgen_intro_forall P :
    (∀ (f : M -> M) (_ : GenTrans f), ⚡={f}=> P) ⊢ ⚡={f}=> (∀ (f : M -> M) (_ : GenTrans f), ⚡={f}=> P).
  Proof.
    iIntros "Hcond".
    iApply bnextgen_forall. iIntros (g).
    iApply bnextgen_forall. iIntros (GenTrans).
    iApply bnextgen_compose. iApply "Hcond".
  Qed.

  Lemma löb_wand_intuitionistically (P : uPredI M) : □ (□ ▷ P -∗ P) ⊢ P.
Proof.
  rewrite -{3}(intuitionistically_elim P) -(löb (□ P)). apply impl_intro_l.
  rewrite {1}intuitionistically_into_persistently_1 later_persistently.
  rewrite persistently_and_intuitionistically_sep_l.
  rewrite -{1}(intuitionistically_idemp (▷ P)) intuitionistically_sep_2.
  by rewrite wand_elim_r.
Qed.

  Lemma löb_wand_plainly (P : uPredI M) `{!Absorbing P} :
    ■ ((■ ▷ P) -∗ P) ⊢ P.
  Proof.
    rewrite -{3}(plainly_elim P) -(löb (■ P)).
    apply impl_intro_l. rewrite later_plainly_1.
    rewrite -{1}(plainly_idemp (▷ P)).
    rewrite -plainly_and plainly_and_sep. rewrite wand_elim_r. auto.
  Qed.

  Lemma löb_wand_plainly_and_intuitionistically (P : uPredI M) `{!Absorbing P} :
    □ ■ ((□ ■ ▷ P) -∗ P) ⊢ P.
  Proof.
    rewrite -{3}(plainly_elim P) -{1}(intuitionistically_elim (■ P)) -(löb (□ ■ P)).
    apply impl_intro_l. rewrite later_intuitionistically later_plainly_1.
    rewrite -{1}(plainly_idemp (▷ P)).
    rewrite -{1}(intuitionistically_idemp (■ ■ ▷ P)).
    rewrite intuitionistically_plainly.
    rewrite and_sep_intuitionistically.
    rewrite intuitionistically_sep_2 -plainly_sep. rewrite wand_elim_r. auto.
  Qed.
    
   
End into_bnextgen.

Section bnextgen_pred.
  Context {M : ucmra} {A : Type} (f : A -> M → M) `{!forall a, CmraMorphism (f a)}.
  
  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; rewrite !uPred_bnextgen_unseal !/uPred_holds /=.

  Lemma bnextgen_pred_intro_forall P a :
    (forall a b, exists c, f a ∘ f b = f c) ->
    (∀ (a : A), ⚡={f a}=> P) ⊢ ⚡={f a}=> (∀ (a : A), ⚡={f a}=> P).
  Proof.
    iIntros (Him) "Hcond".
    iApply bnextgen_forall. iIntros (b).
    iApply bnextgen_compose.
    specialize (Him b a) as [c Hc].
    iApply bnextgen_extensional_eq;[rewrite Hc;eauto|].
    iApply "Hcond".
  Qed.

End bnextgen_pred.

Section bnextgen_inv.
  Context `{!invGS Σ}.
  (* Context (f : M → M) `{!CmraMorphism f}. *)

  Lemma bnextgen_inv N P f `{!CmraMorphism f} :
    inv N P -∗ ⚡={f}=> (inv N (⚡={f}=> P)).
  Proof.
    rewrite invariants.inv_unseal.
    rewrite /invariants.inv_def.
    simpl.
    iIntros "#I".
    rewrite -bnextgen_persistently_2.
    iModIntro.
    rewrite bnextgen_forall.
    iIntros (E).
    iSpecialize ("I" $! E).
  Abort.

End bnextgen_inv.
