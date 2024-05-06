From iris.algebra Require Import functions gmap view gmap_view agree excl csum coPset gset.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own.
From iris.prelude Require Import options.

Import EqNotations. (* Get the [rew] notation. *)

From nextgen Require Import nextgen_basic utils.

(** [TransMap] contains transformation functions for a subset cameras. *)
Definition TransMap Σ : Type := ∀ i, option (R Σ i → R Σ i).


Section transmap.
  Context `{Σ : gFunctors, Ω : gGenCmras Σ}.

  Implicit Types (transmap : TransMap Σ).

  #[global]
  Instance transmap_subseteq : SubsetEq (TransMap Σ) :=
    λ p1 p2, ∀ i t, p1 i = Some t → p2 i = Some t.

End transmap.

Section nextgen_pointwise.
  Context `{Σ : gFunctors}.
  Implicit Types (transmap : TransMap Σ).

  (* Build a global generational transformation based on the transformations in
   * [trans]. *)
  Definition build_trans transmap : iResUR Σ → iResUR Σ :=
    λ (m : iResUR Σ) (i : gid Σ),
      (* Apply the transformation in [transmap], otherwise use id. *)
      let t := default (λ a, a) (transmap i) in
      map_imap (λ γ a, Some (map_unfold (t (map_fold a)))) (m i).
  
  (* We require each transformation in the map to be idempotent *)
  Class TransMapValid transmap :=
    MkValid : ∀ i t, transmap i = Some t → CmraMorphism t ∧ Idemp equiv t.

  #[global]
  Instance build_trans_cmra_morphism transmap :
    TransMapValid transmap → CmraMorphism (build_trans transmap).
  Proof.
    intros V.
    split.
    - intros ??? eq i γ.
      move: (eq i γ).
      rewrite /build_trans.
      rewrite 2!map_lookup_imap.
      destruct (x i !! γ) eqn:look1; destruct (y i !! γ) eqn:look2;
        rewrite look1; rewrite look2; simpl; inversion 1; last done.
      do 2 f_equiv.
      destruct (transmap i) eqn:look3; simpl; last solve_proper.
      specialize (V _ _ look3) as [V _].
      solve_proper.
    - intros ?? val i γ.
      rewrite /build_trans.
      rewrite map_lookup_imap.
      move: (val i γ).
      destruct (x i !! γ) eqn:look; rewrite look; simpl; last done.
      rewrite 2!Some_validN.
      intros val2.
      apply: cmra_morphism_validN.
      destruct (transmap i) eqn:lookT; simpl.
      + specialize (V _ _ lookT) as [V _].
        do 2 apply: cmra_morphism_validN. done.
      + apply: cmra_morphism_validN. done.
    - intros ?.
      rewrite 2!cmra_pcore_core. simpl.
      f_equiv.
      intros i γ.
      rewrite /build_trans.
      rewrite map_lookup_imap.
      rewrite 2!discrete_fun_lookup_core.
      rewrite !lookup_core.
      rewrite map_lookup_imap.
      destruct (x i !! γ) eqn:look; rewrite look; simpl; last done.
      unfold core. simpl.
      rewrite -cmra_morphism_pcore.
      destruct (transmap i) eqn:lookT; simpl.
      + specialize (V _ _ lookT) as [V _].
        rewrite -cmra_morphism_pcore.
        rewrite -cmra_morphism_pcore.
        destruct (pcore c); done.
      + rewrite -cmra_morphism_pcore.
        destruct (pcore c); done.
    - intros ?? i γ.
      unfold build_trans.
      rewrite 2!discrete_fun_lookup_op.
      rewrite map_lookup_imap.
      rewrite 2!lookup_op.
      rewrite 2!map_lookup_imap.
      destruct (x i !! γ) eqn:look1; destruct (y i !! γ) eqn:look2;
        rewrite look1; rewrite look2; simpl; try inversion 1; try done.
      rewrite -Some_op. f_equiv.
      rewrite -cmra_morphism_op. f_equiv.
      destruct (transmap i) eqn:lookT; simpl;
        last by rewrite -cmra_morphism_op.
      specialize (V _ _ lookT) as [V _].
      rewrite -2!cmra_morphism_op.
      done.
  Qed.

  Definition transmap_empty : TransMap Σ :=
    λ i, None.

  (* Build a global generational transformation based on the transformations in
   * [trans]. *)
  Definition transmap_insert (i : gid Σ) (t : R Σ i → R Σ i)
      transmap : TransMap Σ :=
    λ i',
      match decide (i = i') with
        left eq => Some (rew [λ i, _] eq in t)
      | right _ => transmap i'
      end.

  Instance transmap_insert_valid
      `{v : TransMapValid transmap} i t `{!CmraMorphism t} `{!Idemp equiv t} :
    TransMapValid (transmap_insert i t transmap).
  Proof.
    intros i2 ?. unfold transmap_insert.
    destruct (decide (i = i2)) as [eq|]; last apply v.
    intros [= <-]. destruct eq. done.
  Qed.

  Lemma transmap_insert_lookup_eq i t transmap :
    (transmap_insert i t transmap) i = Some t.
  Proof.
    unfold transmap_insert. rewrite decide_True_pi. done.
  Qed.

  Lemma transmap_insert_lookup_ne i1 i2 t transmap :
    i1 ≠ i2 →
    (transmap_insert i1 t transmap) i2 = transmap i2.
  Proof.
    intros neq. unfold transmap_insert. destruct (decide (i1 = i2)); done.
  Qed.

  Lemma transmap_idemp transmap :
    TransMapValid transmap ->
    ∀ x, (build_trans transmap) x ≡ build_trans transmap (build_trans transmap x).
  Proof.
    intros V x i γ.
    rewrite /build_trans.
    rewrite !map_lookup_imap.
    destruct (x i !! γ) eqn:Hlook.
    - rewrite Hlook /=.
      destruct (transmap i) eqn:lookT; simpl;
        [|rewrite map_fold_unfold//].
      specialize (V _ _ lookT) as [V' V].
      f_equiv. f_equiv. rewrite equiv_dist.
      intros n. rewrite map_fold_unfold.
      rewrite V//.
    - rewrite Hlook /= //.
  Qed.

End nextgen_pointwise.

Record gTransformations Σ := GTransformations {
  gT_map : TransMap Σ;
  gT_valid :: TransMapValid gT_map;
}.

Existing Instance gT_valid.

Global Arguments GTransformations {_} _ _.
Global Arguments gT_map {_} _.
Global Arguments gT_valid {_} _.

(* Point-wise nexten with explicit omega. *)
Definition nextgen_omega {Σ} Ω P : iProp Σ :=
  ⚡={build_trans Ω.(gT_map)}=> P.

Notation "⚡={ M }=> P" := (nextgen_omega M P)
  (at level 99, M at level 50, P at level 200, format "⚡={ M }=>  P") : bi_scope.

Notation IntoPnextgen Ω := (IntoBnextgen (build_trans Ω.(gT_map))).

Section nextgen_inG.
  Context {Σ} `{i : inG Σ A}.
  Implicit Types (t : A → A) (ts : iResUR Σ → iResUR Σ).

  (** Lifting of useful lemmas *)
  Lemma transmap_plain (Ω : gTransformations Σ) (P : iProp Σ) `{!Plain P} :
    (⚡={Ω}=> P) ⊢ P.
  Proof.
    apply bnextgen_plain =>//.
  Qed.

  Lemma transmap_sep (Ω : gTransformations Σ) (P Q : iProp Σ) :
    (⚡={Ω}=> P) ∗ (⚡={Ω}=> Q) ⊢ ⚡={Ω}=> P ∗ Q.
  Proof.
    apply bnextgen_sep_2 =>//.
  Qed.

  Lemma transmap_and (Ω : gTransformations Σ) (P Q : iProp Σ) :
    (⚡={Ω}=> P) ∧ (⚡={Ω}=> Q) ⊣⊢ ⚡={Ω}=> P ∧ Q.
  Proof.
    apply bnextgen_and =>//.
  Qed.

  Lemma transmap_big_sepM_1 {K V : Type} `{EqDecision K} `{Countable K} (Ω : gTransformations Σ) (m : gmap K V) (Φ : K -> V -> iProp Σ) :
    ([∗ map] k↦y1 ∈ m, ⚡={Ω}=> Φ k y1) ⊢ ⚡={Ω}=> ([∗ map] k↦y1 ∈ m, Φ k y1).
  Proof.
    apply bnextgen_big_sepM_1 => //.
  Qed.

  Lemma transmap_forall {B} (Ω : gTransformations Σ) Ψ :
    (⚡={Ω}=> (∀ a : B, Ψ a)) ⊣⊢ (∀ a : B, ⚡={Ω}=> Ψ a).
  Proof.
    apply bnextgen_forall.
  Qed.

  Lemma transmap_exists {B} (Ω : gTransformations Σ) Ψ :
    (⚡={Ω}=> (∃ a : B, Ψ a)) ⊣⊢ (∃ a : B, ⚡={Ω}=> Ψ a).
  Proof.
    apply bnextgen_exist.
  Qed.

  Lemma transmap_later (Ω : gTransformations Σ) Ψ :
    (⚡={Ω}=> (▷ Ψ)) ⊣⊢ (▷ ⚡={Ω}=> Ψ).
  Proof.
    rewrite bnextgen_later. auto.
  Qed.

  Lemma transmap_or (Ω : gTransformations Σ) (P Q : iProp Σ) :
    (⚡={Ω}=> P) ∨ (⚡={Ω}=> Q) ⊣⊢ ⚡={Ω}=> P ∨ Q.
  Proof.
    apply bnextgen_or =>//.
  Qed.

  Lemma transmap_wand_plainly (Ω : gTransformations Σ) (P Q : iProp Σ) :
    (⚡={Ω}=> (■ P -∗ Q)) ⊣⊢ (■ P -∗ ⚡={Ω}=> Q).
  Proof.
    apply bnextgen_wand_plainly.
  Qed.

  Lemma transmap_wand_plain (Ω : gTransformations Σ) P `{!Plain P, !Absorbing P} Q :
    (⚡={Ω}=> (P -∗ Q)) ⊣⊢ (P -∗ ⚡={Ω}=> Q).
  Proof.
    apply bnextgen_wand_plain;auto.
  Qed.

  Lemma transmap_impl_plain (Ω : gTransformations Σ) P `{!Plain P, !Absorbing P} Q :
    (⚡={Ω}=> (P → Q)) ⊣⊢ (P → ⚡={Ω}=> Q).
  Proof.
    apply bnextgen_impl_plain;auto.
  Qed.

  Lemma transmap_persistently (Ω : gTransformations Σ) (P : iProp Σ) :
    (□ ⚡={Ω}=> P) ⊣⊢ (⚡={Ω}=> □ P).
  Proof.
    apply bnextgen_persistently.
  Qed.

  Lemma transmap_if_persistently (Ω : gTransformations Σ) (P : iProp Σ) (b : bool) :
    (□?b ⚡={Ω}=> P) ⊣⊢ (⚡={Ω}=> □?b P).
  Proof.
    destruct b;simpl;auto.
    apply bnextgen_persistently.
  Qed.

  Global Instance transmap_proper (Ω : gTransformations Σ) :
    Proper ((≡) ==> (≡)) (nextgen_omega Ω).
  Proof. intros ???. by apply bnextgen_proper. Qed.

  Lemma transmap_omega_idemp (Ω : gTransformations Σ) (P : iProp Σ) :
    (⚡={Ω}=> P) ⊣⊢ (⚡={Ω}=> ⚡={Ω}=> P).
  Proof.
    iApply bnextgen_idemp.
    apply transmap_idemp. apply _.
  Qed.

  Lemma transmap_own_lookup_Some {Ω} γ a t `{!CmraMorphism t} :
    Ω.(gT_map) i.(inG_id) = Some (cmra_map_transport inG_prf t) →
    own γ a ⊢ ⚡={Ω}=> own γ (t a).
  Proof.
    intros look.
    iIntros "H".
    rewrite /nextgen_omega own.own_eq /own.own_def.
    iModIntro.
    rewrite /build_trans.
    unfold own.iRes_singleton.
    iApply uPred.ownM_mono; last iApply "H".
    apply discrete_fun_included_spec => id.
    destruct (decide (inG_id i = id)) as [<-|]; last first.
    { rewrite discrete_fun_lookup_singleton_ne; done. }
    rewrite 2!discrete_fun_lookup_singleton.
    apply singleton_included_l.
    eexists _.
    split.
    - rewrite map_lookup_imap.
      rewrite lookup_singleton.
      simpl.
      f_equiv. reflexivity.
    - apply Some_included. left.
      rewrite -(map_unfold_inG_unfold _).
      rewrite look. simpl.
      f_equiv.
      specialize (@map_unfold_inG_unfold _ A i) as eq.
      rewrite -(map_unfold_inG_unfold _).
      rewrite map_fold_unfold.
      rewrite -cmra_map_transport_cmra_transport.
      done.
  Qed.

  Lemma transmap_own_lookup_None {Ω} γ (a : A) :
    Ω.(gT_map) i.(inG_id) = None →
    own γ a ⊢ ⚡={Ω}=> own γ a.
  Proof.
    intros look.
    iIntros "H".
    rewrite /nextgen_omega own.own_eq /own.own_def.
    iModIntro.
    rewrite /build_trans.
    unfold own.iRes_singleton.
    iApply uPred.ownM_mono; last iApply "H".
    apply discrete_fun_included_spec => id.
    destruct (decide (inG_id i = id)) as [<-|]; last first.
    { rewrite discrete_fun_lookup_singleton_ne; done. }
    rewrite 1!discrete_fun_lookup_singleton.
    apply singleton_included_l.
    eexists _.
    split.
    - rewrite map_lookup_imap.
      rewrite lookup_singleton.
      simpl.
      f_equiv. reflexivity.
    - apply Some_included. left.
      rewrite look. simpl.
      rewrite -(map_unfold_inG_unfold _).
      f_equiv.
      rewrite map_fold_unfold.
      done.
  Qed.

  Program Definition transmap_insert_inG (t : A → A) `{!CmraMorphism t} `{!Idemp equiv t} Ω :=
    GTransformations
      (transmap_insert i.(inG_id) (cmra_map_transport inG_prf t) Ω.(gT_map))
      (transmap_insert_valid _ _).

End nextgen_inG.

Definition transmap_insert_two_inG {A B : cmra} `{i:inG Σ A} `{j:inG Σ B}
  (t : A → A) (f : B -> B) `{!CmraMorphism t} `{!CmraMorphism f}
  `{!Idemp equiv t} `{!Idemp equiv f} Ω :=
  transmap_insert_inG t (transmap_insert_inG f Ω).

(*
(* Point-wise nexten with implicit omega. *)
Definition nextgen {Σ Ω} P : iProp Σ :=
  ⚡={Ω}=> P.

Notation "⚡==> P" := (nextgen P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.
 *)

(* Knowledge about the camera [A] and an associated transformation [t]. *)
Class transInG Σ (Ω : gTransformations Σ) (A : cmra) (t : A → A) `{!CmraMorphism t} := {
  genInG_inG :: inG Σ A;
  genInG_trans_lookup :
    Ω.(gT_map) genInG_inG.(inG_id) = Some (cmra_map_transport inG_prf t)
  }.

(* Knowledge about the camera [A] and the fact that it is unaffected by
 * generations. The name is an abbreviation of "generationally independent
 * inG". Maybe not the best name 🙂 *)
Notation genIndInG Σ Ω A := (transInG Σ Ω A id).

(* Knowledge about the camera [A] and the fact that there is no associated. *)
Class noTransInG Σ (Ω : gTransformations Σ) (A : cmra) := {
  noTransInG_inG :: inG Σ A;
  noTransInG_trans_lookup : Ω.(gT_map) noTransInG_inG.(inG_id) = None
  }.

(* Knowledge about the camera [A] and [B], the fact that there is no
associated transformations, and that their gid's are different *)
Class noTwoTransInG Σ (Ω : gTransformations Σ) (A : cmra) (B : cmra) := {
    noTransInG_A_inG :: noTransInG Σ Ω A;
    noTransInG_B_inG :: noTransInG Σ Ω B;
    noTransInG_diff : (noTransInG_A_inG.(noTransInG_inG)).(inG_id) ≠ (noTransInG_B_inG.(noTransInG_inG)).(inG_id)
}.

(* #[global] Instance noTransInG_inl `{no_trans : noTwoTransInG Σ Ω A B} : noTransInG Σ Ω A.  *)
(*   {| noTransInG_inG := no_trans.(noTransInG_A_inG) ; noTransInG_trans_lookup := no_trans.(noTransInG_trans_A_lookup) |}. *)

(* #[global] Instance noTransInG_inr `{no_trans : noTwoTransInG Σ Ω A B} : noTransInG Σ Ω B := *)
(*   {| noTransInG_inG := no_trans.(noTransInG_B_inG) ; noTransInG_trans_lookup := no_trans.(noTransInG_trans_B_lookup) |}. *)

Section nextgen_instances.

  Lemma transmap_own_trans `{transInG Σ Ω A t} γ a :
    own γ a ⊢ ⚡={Ω}=> own γ (t a).
  Proof. iApply transmap_own_lookup_Some. apply genInG_trans_lookup. Qed.

  #[global]
  Instance into_pnextgen_own `{transInG Σ Ω A t} γ a :
      IntoPnextgen Ω _ _ :=
    transmap_own_trans γ a.

  Lemma transmap_own_ind `{!genIndInG Σ Ω A} γ (a : A) :
    own γ a ⊢ ⚡={Ω}=> own γ a.
  Proof. iIntros "O". iModIntro. done. Qed.

  #[global]
  Instance into_pnextgen_own_ind `{genIndInG Σ Ω A} γ a :
      IntoPnextgen Ω _ _ :=
    transmap_own_ind γ a.

  Lemma transmap_own_insert_other {A1 A2}
    `{i : noTransInG Σ Ω A1} (t1 : A1 → A1) `{!CmraMorphism t1}
    `{!CmraMorphism t2} `{!transInG Σ Ω A2 t2} γ (a : A2)
    `{!Idemp equiv t1}:
    own γ a ⊢ ⚡={transmap_insert_inG t1 Ω}=> own γ (t2 a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_ne; cycle 1.
    { specialize noTransInG_trans_lookup as look1.
      specialize genInG_trans_lookup as look2.
      intros eq. rewrite eq in look1.
      rewrite look1 in look2.
      done. }
    apply genInG_trans_lookup.
  Qed.

  #[global]
  Instance into_pnextgen_insert_own_other {A1 A2}
    `{i : noTransInG Σ Ω A1} (t1 : A1 → A1) `{!CmraMorphism t1}
    `{!CmraMorphism t2} `{!transInG Σ Ω A2 t2} γ (a : A2) `{!Idemp equiv t1} :
      IntoPnextgen _ _ _ :=
    transmap_own_insert_other t1 γ a.

  #[global]
  Instance into_pnextgen_insert_other_ind {A1 A2}
    `{i : noTransInG Σ Ω A1} (t1 : A1 → A1) `{!CmraMorphism t1}
    `{!genIndInG Σ Ω A2} γ (a : A2) `{!Idemp equiv t1} :
      IntoPnextgen _ _ (own γ a) :=
    transmap_own_insert_other t1 γ a.

  Lemma transmap_own_insert {A}
    `{i : noTransInG Σ Ω A} (t : A → A) `{!CmraMorphism t} `{!Idemp equiv t} γ (a : A) :
    own γ a ⊢ ⚡={transmap_insert_inG t Ω}=> own γ (t a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_eq.
    done.
  Qed.

  Lemma bnextgen_extensional_eq_iprop {Σ} P (f g : iResUR Σ -> iResUR Σ) `{!CmraMorphism f} `{!CmraMorphism g} :
    (forall x i0, f x i0 ≡ g x i0) ->
    (uPred_bnextgen f P) ⊣⊢ uPred_bnextgen g P.
  Proof.
    intros Hext.
    split; intros. try uPred.unseal; rewrite  /uPred_bnextgen seal_eq;
      rewrite !/uPred_holds /=.
    destruct P. rewrite /upred.uPred_holds.
    split;intros.
    - eapply uPred_mono;eauto. exists ε. simpl.
      intros i. rewrite -Hext.
      pose proof (ucmra_unit_right_id (f x)) as Heq. clear H H0.
      specialize (Heq i). rewrite Heq. auto.
    - eapply uPred_mono;eauto. exists ε. simpl.
      intros i. rewrite Hext.
      pose proof (ucmra_unit_right_id (g x)) as Heq. clear H H0.
      specialize (Heq i). rewrite Heq. auto.
  Qed.
  
  Lemma transmap_insert_extensional_eq {A} `{i : noTransInG Σ Ω A} (t : A → A)
    (g : A -> A) (C1 : CmraMorphism t) (C2 : CmraMorphism g)
    `{!Idemp equiv t} `{!Idemp equiv g} P :
    (forall (x : A), t x ≡ g x) ->
    (⚡={transmap_insert_inG t Ω}=> P) ⊣⊢ ⚡={transmap_insert_inG g Ω}=> P.
  Proof.
    intros Hext.
    apply bnextgen_extensional_eq_iprop.
    intros. simpl. unfold build_trans.
    erewrite map_imap_ext;eauto.
    simpl. intros.
    destruct (x i0 !! k) eqn:Hlook;rewrite Hlook /= //. rewrite /transmap_insert.
    destruct (decide (inG_id noTransInG_inG = i0));auto. simplify_eq.
    destruct i. destruct noTransInG_inG0;simpl in *. subst A.
    simpl in *. rewrite Hext. auto.
  Qed.

  Lemma two_transmap_swap {A1 A2} `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) (t2 : A2 -> A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2} (P : iProp Σ)
    `{!Idemp equiv t1} `{!Idemp equiv t2} :
    (⚡={transmap_insert_inG t1 Ω}=> ⚡={transmap_insert_inG t2 Ω}=> P) ⊣⊢ ⚡={transmap_insert_inG t2 Ω}=> ⚡={transmap_insert_inG t1 Ω}=> P.
  Proof.
    split; intros. rewrite /nextgen_omega. try uPred.unseal; rewrite  /uPred_bnextgen seal_eq;
      rewrite !/uPred_holds /=.
    destruct P. rewrite /upred.uPred_holds.
    split;intros; simpl in *.
    - eapply uPred_mono;eauto.
      rewrite /build_trans. exists ε. rewrite ucmra_unit_right_id. simpl.
      intros i' γ.
      rewrite !map_imap_compose.
      rewrite !map_lookup_imap.
      destruct (x i' !! γ) eqn:Hsome;rewrite Hsome// /=. f_equiv.
      destruct (decide (inG_id noTransInG_inG = i')).
      + subst i'. pose proof noTransInG_diff.
        rewrite transmap_insert_lookup_eq.
        rewrite transmap_insert_lookup_ne//.
        f_equiv. rewrite !noTransInG_trans_lookup /=.
        rewrite !map_fold_unfold. auto.
      + destruct (decide (inG_id (@noTransInG_inG Σ Ω _ noTransInG_A_inG) = i')).
        * subst i'. pose proof noTransInG_diff.
        rewrite transmap_insert_lookup_eq.
        rewrite transmap_insert_lookup_ne//.
        f_equiv. rewrite !noTransInG_trans_lookup /=.
        rewrite !map_fold_unfold. auto.
        * rewrite !transmap_insert_lookup_ne//.
    - eapply uPred_mono;eauto.
      rewrite /build_trans. exists ε. rewrite ucmra_unit_right_id. simpl.
      intros i' γ.
      rewrite !map_imap_compose.
      rewrite !map_lookup_imap.
      destruct (x i' !! γ) eqn:Hsome;rewrite Hsome// /=. f_equiv.
      destruct (decide (inG_id noTransInG_inG = i')).
      + subst i'. pose proof noTransInG_diff.
        rewrite transmap_insert_lookup_eq.
        rewrite transmap_insert_lookup_ne//.
        f_equiv. rewrite !noTransInG_trans_lookup /=.
        rewrite !map_fold_unfold. auto.
      + destruct (decide (inG_id (@noTransInG_inG Σ Ω _ noTransInG_A_inG) = i')).
        * subst i'. pose proof noTransInG_diff.
        rewrite transmap_insert_lookup_eq.
        rewrite transmap_insert_lookup_ne//.
        f_equiv. rewrite !noTransInG_trans_lookup /=.
        rewrite !map_fold_unfold. auto.
        * rewrite !transmap_insert_lookup_ne//.
  Qed.

  #[global]
    Instance Idemp_compose {A : cmra} (t1 : A → A) (t2 : A -> A)
    `{!Idemp equiv t1} `{!Idemp equiv t2} `{!Indep equiv t1 t2}
    `{!NonExpansive t1} `{!NonExpansive t2} :
    Idemp equiv (t2 ∘ t1).
  Proof.
    intros a. simpl.
    rewrite -{2}(Idemp1 (t1 a)).
    apply equiv_dist. intros n.
    f_equiv.
    rewrite -{2}(Indep0 a).
    rewrite -(Idemp0 (t2 a)).
    f_equiv.
    rewrite (Indep0 a).
    auto.
  Qed.
    
  Lemma transmap_insert_compose {A} `{i : noTransInG Σ Ω A} (t1 : A → A) (t2 : A -> A)
    `{!CmraMorphism t1} `{!CmraMorphism t2} (P : iProp Σ)
    `{!Idemp equiv t1} `{!Idemp equiv t2} `{!Indep equiv t1 t2} :
    (⚡={transmap_insert_inG t1 Ω}=> ⚡={transmap_insert_inG t2 Ω}=> P) ⊣⊢ ⚡={transmap_insert_inG (t2 ∘ t1) Ω}=> P.
  Proof.
    split; intros. rewrite /nextgen_omega. try uPred.unseal; rewrite  /uPred_bnextgen seal_eq;
      rewrite !/uPred_holds /=.
    destruct P. rewrite /upred.uPred_holds.
    split;intros; simpl in *.
    - eapply uPred_mono;eauto.
      rewrite /build_trans. exists ε. rewrite ucmra_unit_right_id. simpl.
      intros i' γ.
      rewrite !map_imap_compose.
      rewrite !map_lookup_imap.
      destruct (x i' !! γ) eqn:Hsome;rewrite Hsome// /=. f_equiv.
      destruct (decide (inG_id noTransInG_inG = i')).
      + subst i'.
        rewrite !transmap_insert_lookup_eq//.
        f_equiv. simpl.
        rewrite !map_fold_unfold.
        rewrite -cmra_map_transport_compose//.
      + rewrite !transmap_insert_lookup_ne// /=.
        f_equiv. rewrite /default.
        destruct (gT_map Ω i') eqn:Hc;[|rewrite map_fold_unfold//].
        simpl.
        pose proof (gT_valid _ _ _ Hc) as [V1 V2].
        rewrite - (V2 (map_fold c)).
        apply cmra_morphism_ne. rewrite map_fold_unfold.
        rewrite V2. auto.
    - eapply uPred_mono;eauto.
      rewrite /build_trans. exists ε. rewrite ucmra_unit_right_id. simpl.
      intros i' γ.
      rewrite !map_imap_compose.
      rewrite !map_lookup_imap.
      destruct (x i' !! γ) eqn:Hsome;rewrite Hsome// /=. f_equiv.
      destruct (decide (inG_id noTransInG_inG = i')).
      + subst i'.
        rewrite !transmap_insert_lookup_eq. f_equiv.
        rewrite !map_fold_unfold /=.
        rewrite cmra_map_transport_compose. auto.
      + rewrite !transmap_insert_lookup_ne// /=.
        f_equiv. rewrite /default /=.
        destruct (gT_map Ω i') eqn:Hc;[|rewrite map_fold_unfold//].
        pose proof (gT_valid _ _ _ Hc) as [V1 V2].
        rewrite map_fold_unfold.
        rewrite V2. auto.
  Qed.
  
  #[global]
  Instance into_pnextgen_own_insert {A}
      `{i : noTransInG Σ Ω A} (t : A → A) `{!CmraMorphism t} `{!Idemp equiv t} γ (a : A) :
      IntoPnextgen _ _ _ :=
    transmap_own_insert t γ a.

   Lemma transmap_own_insert_other_left {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A2 → A2) `{!CmraMorphism t1} `{!Idemp equiv t1} γ (a : A1) :
    own γ a ⊢ ⚡={transmap_insert_inG t1 Ω}=> own γ a.
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_None; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_ne; cycle 1.
    { by specialize  noTransInG_diff as Hdiff. }
    apply noTransInG_trans_lookup.
  Qed.

  Lemma transmap_own_insert_other_right {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) `{!CmraMorphism t1} `{!Idemp equiv t1} γ (a : A2) :
    own γ a ⊢ ⚡={transmap_insert_inG t1 Ω}=> own γ a.
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_None; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_ne; cycle 1.
    { by specialize  noTransInG_diff as Hdiff. }
    apply noTransInG_trans_lookup.
  Qed.

  Lemma transmap_own_insert_left {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) `{!CmraMorphism t1} `{!Idemp equiv t1} γ (a : A1) :
    own γ a ⊢ ⚡={transmap_insert_inG t1 Ω}=> own γ (t1 a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_eq//.
  Qed.

  Lemma transmap_own_insert_right {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t2 : A2 → A2) `{!CmraMorphism t2} `{!Idemp equiv t2} γ (a : A2) :
    own γ a ⊢ ⚡={transmap_insert_inG t2 Ω}=> own γ (t2 a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_eq//.
  Qed.

  Lemma transmap_own_insert_two_left {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) (t2 : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2} `{!Idemp equiv t1}
    `{!Idemp equiv t2} γ (a : A1) :
    own γ a ⊢ ⚡={transmap_insert_two_inG t1 t2 Ω}=> own γ (t1 a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_two_inG. simpl.
    rewrite transmap_insert_lookup_eq; auto.
  Qed.

  Lemma transmap_own_insert_two_right {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) (t2 : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2}
    `{!Idemp equiv t1} `{!Idemp equiv t2} γ (a : A2) :
    own γ a ⊢ ⚡={transmap_insert_two_inG t1 t2 Ω}=> own γ (t2 a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_two_inG. simpl.
    rewrite transmap_insert_lookup_ne;cycle 1.
    { by specialize (noTransInG_diff). }
    rewrite transmap_insert_lookup_eq; auto.
  Qed.

  Lemma transmap_own_insert_two_other {A1 A2 A3}
    `{i : noTwoTransInG Σ Ω A1 A2} `{j: transInG Σ Ω A3 t3} (t1 : A1 → A1) (t2 : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2}
    `{!Idemp equiv t1} `{!Idemp equiv t2} γ (a : A3) :
    own γ a ⊢ ⚡={transmap_insert_two_inG t1 t2 Ω}=> own γ (t3 a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_two_inG. simpl.
    rewrite !transmap_insert_lookup_ne; auto.
    { apply genInG_trans_lookup. }
    { specialize noTransInG_trans_lookup as look1.
      specialize genInG_trans_lookup as look2.
      intros eq. rewrite eq in look1.
      rewrite look1 in look2.
      done. }
    { specialize (@noTransInG_trans_lookup Σ Ω A1 _) as look1.
      specialize genInG_trans_lookup as look2.
      intros eq. rewrite eq in look1.
      rewrite look1 in look2.
      done. }    
  Qed.


  Lemma build_trans_two_insert_extensional_eq_left {A B}
    `{i : noTwoTransInG Σ Ω A B} (t : A → A)
    (g : A -> A) (f : B -> B) (C1 : CmraMorphism t) (C2 : CmraMorphism g)
    (C3 : CmraMorphism f)
    `{!Idemp equiv t} `{!Idemp equiv g}
    `{!Idemp equiv f} n (x : iResUR Σ) (i0 : fin (gFunctors_len Σ)) :
    (forall (x : A), t x ≡ g x) ->
      build_trans
        (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t)
           (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf f) (gT_map Ω))) x i0 ≡{n}≡ 
        build_trans
        (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf g)
           (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf f) (gT_map Ω))) x i0.
  Proof.
    intros Hext. simpl.
    intros. simpl. unfold build_trans.
    erewrite map_imap_ext;eauto.
    simpl. intros.
    destruct (x i0 !! k) eqn:Hlook;rewrite Hlook /= //. rewrite /transmap_insert.
    destruct (decide (inG_id noTransInG_inG = i0));auto. simplify_eq.
    destruct i. simpl. destruct noTransInG_A_inG0;simpl in *.
    destruct noTransInG_inG0. subst A. simpl in *.
    rewrite Hext. auto.
  Qed.
    
  Lemma transmap_two_insert_extensional_eq_left {A B}
    `{i : noTwoTransInG Σ Ω A B} (t : A → A)
    (g : A -> A) (f : B -> B) (C1 : CmraMorphism t) (C2 : CmraMorphism g)
    (C3 : CmraMorphism f)
    `{!Idemp equiv t} `{!Idemp equiv g}
    `{!Idemp equiv f} P :
    (forall (x : A), t x ≡ g x) ->
    (⚡={transmap_insert_two_inG t f Ω}=> P) ⊣⊢ ⚡={transmap_insert_two_inG g f Ω}=> P.
  Proof.
    intros Hext.
    apply bnextgen_extensional_eq_iprop.
    intros x i0. apply equiv_dist=>n.
    apply build_trans_two_insert_extensional_eq_left;auto.
  Qed.

  Lemma build_trans_two_insert_extensional_eq_right {A B}
    `{i : noTwoTransInG Σ Ω A B} (t : B → B)
    (g : B -> B) (f : A -> A) (C1 : CmraMorphism t) (C2 : CmraMorphism g)
    (C3 : CmraMorphism f)
    `{!Idemp equiv t} `{!Idemp equiv g}
    `{!Idemp equiv f} n (x : iResUR Σ) (i0 : fin (gFunctors_len Σ)):
    (forall (x : B), t x ≡ g x) ->
      build_trans
        (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf f)
           (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t) (gT_map Ω))) x i0 ≡{n}≡ 
        build_trans
        (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf f)
           (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf g) (gT_map Ω))) x i0.
  Proof.
    intros Hext.
    intros. simpl. unfold build_trans.
    erewrite map_imap_ext;eauto.
    simpl. intros.
    destruct (x i0 !! k) eqn:Hlook;rewrite Hlook /= //. rewrite /transmap_insert.
    destruct (decide (inG_id noTransInG_inG = i0));auto.
    case_match;auto.
    simplify_eq.
    destruct i. simpl. destruct noTransInG_B_inG0;simpl in *.
    destruct noTransInG_inG0. subst B. simpl in *.
    rewrite Hext. auto.
  Qed.

  Lemma build_trans_two_insert_extensional_eq {A B}
    `{i : noTwoTransInG Σ Ω A B} (t1 : A → A) (t2 : A → A)
    (g1 : B -> B) (g2 : B -> B) (C1 : CmraMorphism t1) (C2 : CmraMorphism t2) (C3 : CmraMorphism g1)
    (C4 : CmraMorphism g2)
    `{!Idemp equiv t1} `{!Idemp equiv t2} `{!Idemp equiv g1}
    `{!Idemp equiv g2} n (x : iResUR Σ) (i0 : fin (gFunctors_len Σ)) :
    (forall (x : A), t1 x ≡ t2 x) ->
    (forall (x : B), g1 x ≡ g2 x) ->
      build_trans
        (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t1)
           (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf g1) (gT_map Ω))) x i0 ≡{n}≡ 
        build_trans
        (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2)
           (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf g2) (gT_map Ω))) x i0.
  Proof.
    intros Hext.
    intros.
    rewrite build_trans_two_insert_extensional_eq_right;auto.
    rewrite build_trans_two_insert_extensional_eq_left;auto.
  Qed.
    
  Lemma transmap_two_insert_extensional_eq_right {A B}
    `{i : noTwoTransInG Σ Ω A B} (t : B → B)
    (g : B -> B) (f : A -> A) (C1 : CmraMorphism t) (C2 : CmraMorphism g)
    (C3 : CmraMorphism f)
    `{!Idemp equiv t} `{!Idemp equiv g}
    `{!Idemp equiv f} P :
    (forall (x : B), t x ≡ g x) ->
    (⚡={transmap_insert_two_inG f t Ω}=> P) ⊣⊢ ⚡={transmap_insert_two_inG f g Ω}=> P.
  Proof.
    intros Hext.
    apply bnextgen_extensional_eq_iprop.
    intros x i0. apply equiv_dist=>n.
    apply build_trans_two_insert_extensional_eq_right;auto.
  Qed.

  Lemma build_trans_two_insert_compose {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) (t1' : A1 → A1)
    (t2 : A2 → A2) (t2' : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2} `{!CmraMorphism t1'} `{!CmraMorphism t2'}
    `{!Idemp equiv t1} `{!Idemp equiv t1'}
    `{!Idemp equiv t2} `{!Idemp equiv t2'}
    `{!Indep equiv t1 t1'} `{!Indep equiv t2 t2'} n x :
    build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (t1' ∘ t1))
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (t2' ∘ t2)) (gT_map Ω))) x ≡{n}≡ 
      build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t1')
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2') (gT_map Ω)))
      (build_trans
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t1)
            (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2) (gT_map Ω))) x).
  Proof.
    rewrite /build_trans. simpl.
    intros i' γ.
    rewrite !map_imap_compose.
    rewrite !map_lookup_imap.
    destruct (x i' !! γ) eqn:Hsome;rewrite Hsome// /=. f_equiv.
    pose proof noTransInG_diff.
    destruct (decide (inG_id noTransInG_inG = i')).
    + subst i'.
      repeat rewrite transmap_insert_lookup_ne//
        !transmap_insert_lookup_eq//.
      f_equiv. simpl.
      rewrite !map_fold_unfold.
      rewrite -cmra_map_transport_compose//.
    + destruct (decide (inG_id (@noTransInG_inG Σ Ω _ noTransInG_A_inG) = i')).
      * subst i'.
        rewrite !transmap_insert_lookup_eq. simpl.
        f_equiv. simpl. rewrite !map_fold_unfold.
        rewrite -cmra_map_transport_compose//.
      * rewrite !transmap_insert_lookup_ne// /default.
        destruct (gT_map Ω i') eqn:Hc;[|rewrite map_fold_unfold//].
        simpl. pose proof (gT_valid _ _ _ Hc) as [V1 V2].
        rewrite map_fold_unfold.
        rewrite V2. auto.
  Qed.

  Lemma build_trans_insert_id {A1} `{i : noTransInG Σ Ω A1} x :
    build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (id : A1 -> A1)) (gT_map Ω)) x
      ≡ build_trans (gT_map Ω) x.
  Proof.
    unfold build_trans. intros i0.
    erewrite map_imap_ext;eauto.
    simpl. intros.
    destruct (x i0 !! k) eqn:Hlook;rewrite Hlook /= //.
    rewrite /transmap_insert.
    destruct (decide (inG_id noTransInG_inG = i0));auto.
    simpl.  subst i0. simpl. destruct i.
    destruct noTransInG_inG0. subst A1. simpl in *.
    rewrite /default. rewrite noTransInG_trans_lookup0.
    auto.
  Qed.
  
  Lemma build_trans_two_insert_compose_left {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) (t1' : A1 → A1)
    (t2 : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2} `{!CmraMorphism t1'}
    `{!Idemp equiv t1} `{!Idemp equiv t1'}
    `{!Idemp equiv t2} 
    `{!Indep equiv t1 t1'} n x :
    build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (t1' ∘ t1))
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2) (gT_map Ω))) x ≡{n}≡ 
      build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t1')
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf id) (gT_map Ω)))
      (build_trans
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t1)
            (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2) (gT_map Ω))) x).
  Proof.
    assert (t2 = id ∘ t2) as Heq;[auto|].
    rewrite {1}Heq.
    apply build_trans_two_insert_compose;auto;try apply _.
    - intros ?. auto.
    - intros ?. auto.
  Qed.

  Lemma build_trans_two_insert_compose_right {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1)
    (t2 : A2 → A2) (t2' : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2} `{!CmraMorphism t2'}
    `{!Idemp equiv t1}
    `{!Idemp equiv t2} `{!Idemp equiv t2'}
    `{!Indep equiv t2 t2'} n x :
    build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (t1))
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (t2' ∘ t2)) (gT_map Ω))) x ≡{n}≡ 
      build_trans
      (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf (id : A1 -> A1))
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2') (gT_map Ω)))
      (build_trans
         (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t1)
            (transmap_insert (inG_id noTransInG_inG) (cmra_map_transport inG_prf t2) (gT_map Ω))) x).
  Proof.
    assert (t1 = id ∘ t1) as Heq;[auto|].
    rewrite {1}Heq.
    apply build_trans_two_insert_compose; auto;try apply _.
    - intros ?. auto.
    - intros ?. auto.
  Qed.
    
  Lemma transmap_two_insert_compose {A1 A2}
    `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) (t1' : A1 → A1)
    (t2 : A2 → A2) (t2' : A2 → A2)
    `{!CmraMorphism t1} `{!CmraMorphism t2} `{!CmraMorphism t1'} `{!CmraMorphism t2'}
    (P : iProp Σ)
    `{!Idemp equiv t1} `{!Idemp equiv t1'}
    `{!Idemp equiv t2} `{!Idemp equiv t2'}
    `{!Indep equiv t1 t1'} `{!Indep equiv t2 t2'} :
    (⚡={transmap_insert_two_inG t1 t2 Ω}=> ⚡={transmap_insert_two_inG t1' t2' Ω}=> P) ⊣⊢
      ⚡={transmap_insert_two_inG (t1' ∘ t1) (t2' ∘ t2) Ω}=> P.
  Proof.
    split; intros. rewrite /nextgen_omega. try uPred.unseal; rewrite  /uPred_bnextgen seal_eq;
      rewrite !/uPred_holds /=.
    destruct P. rewrite /upred.uPred_holds.
    split;intros; simpl in *.
    - eapply uPred_mono;eauto.
      exists ε. rewrite ucmra_unit_right_id.
      apply build_trans_two_insert_compose;auto.
    - eapply uPred_mono;eauto.
      exists ε. rewrite ucmra_unit_right_id.
      symmetry. apply build_trans_two_insert_compose;auto.
  Qed.    
    
  #[global]
  Instance into_pnextgen_insert_own_other_left {A1 A2}
  `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A2 → A2) `{!CmraMorphism t1}
  `{!Idemp equiv t1}
    γ (a : A1) :
      IntoPnextgen _ _ _ | 2 :=
    transmap_own_insert_other_left t1 γ a.

  #[global]
  Instance into_pnextgen_insert_own_other_right {A1 A2}
  `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) `{!CmraMorphism t1}
  `{!Idemp equiv t1}
    γ (a : A2) :
      IntoPnextgen _ _ _ | 2 :=
    transmap_own_insert_other_right t1 γ a.

  #[global]
  Instance into_pnextgen_insert_other_left_ind {A1 A2}
  `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A2 → A2) `{!CmraMorphism t1}
  `{!Idemp equiv t1}
    γ (a : A1) :
      IntoPnextgen _ _ (own γ a) | 2 :=
    transmap_own_insert_other_left t1 γ a.

  #[global]
  Instance into_pnextgen_insert_other_right_ind {A1 A2}
  `{i : noTwoTransInG Σ Ω A1 A2} (t1 : A1 → A1) `{!CmraMorphism t1}
  `{!Idemp equiv t1}
    γ (a : A2) :
      IntoPnextgen _ _ (own γ a) | 2 :=
    transmap_own_insert_other_right t1 γ a.

End nextgen_instances.

Section test.
  Context `{noTransInG Σ Ω A}.
  Context (t : A → A) `{!CmraMorphism t} `{!Idemp equiv t}.
  Context `{genIndInG Σ Ω B}.
  Context `{transInG Σ Ω C tC}.

  Lemma test γ1 (a : A) γ2 (b : B) γ3 (c : C) :
    own γ1 a -∗
    own γ2 b -∗
    own γ3 c -∗
    ⚡={transmap_insert_inG t Ω}=>
      own γ1 (t a) ∗
      own γ2 b ∗
      own γ3 (tC c).
  Proof.
    iIntros "O1 O2 O3".
    iModIntro.
    iFrame.
  Qed.

End test.
