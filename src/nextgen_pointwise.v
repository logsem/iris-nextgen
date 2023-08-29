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

  Class TransMapValid transmap :=
    MkValid : ∀ i t, transmap i = Some t → CmraMorphism t.

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
      specialize (V _ _ look3).
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
      + specialize (V _ _ lookT).
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
      + specialize (V _ _ lookT).
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
      specialize (V _ _ lookT).
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
      `{v : TransMapValid transmap} i t `{!CmraMorphism t} :
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

End nextgen_pointwise.

Record gTransformations Σ := GTransformations {
  gT_map : TransMap Σ;
  gT_valid :> TransMapValid gT_map;
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

  Lemma transmap_sep (Ω : gTransformations Σ) (P Q : iProp Σ) `{!Plain P} :
    (⚡={Ω}=> P) ∗ (⚡={Ω}=> Q) ⊢ ⚡={Ω}=> P ∗ Q.
  Proof.
    apply bnextgen_sep_2 =>//.
  Qed.

  Lemma transmap_big_sepM_1 {K V : Type} `{EqDecision K} `{Countable K} (Ω : gTransformations Σ) (m : gmap K V) (Φ : K -> V -> iProp Σ) :
    ([∗ map] k↦y1 ∈ m, ⚡={Ω}=> Φ k y1) ⊢ ⚡={Ω}=> ([∗ map] k↦y1 ∈ m, Φ k y1).
  Proof.
    apply bnextgen_big_sepM_1 => //.
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

  Definition transmap_insert_inG (t : A → A) `{!CmraMorphism t} Ω :=
    GTransformations
      (transmap_insert i.(inG_id) (cmra_map_transport inG_prf t) Ω.(gT_map))
      (transmap_insert_valid _ _).

End nextgen_inG.

(*
(* Point-wise nexten with implicit omega. *)
Definition nextgen {Σ Ω} P : iProp Σ :=
  ⚡={Ω}=> P.

Notation "⚡==> P" := (nextgen P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.
 *)

(* Knowledge about the camera [A] and an associated transformation [t]. *)
Class transInG Σ (Ω : gTransformations Σ) (A : cmra) (t : A → A) `{!CmraMorphism t} := {
  genInG_inG :> inG Σ A;
  genInG_trans_lookup :
    Ω.(gT_map) genInG_inG.(inG_id) = Some (cmra_map_transport inG_prf t)
}.

(* Knowledge about the camera [A] and the fact that it is unaffected by
 * generations. The name is an abbreviation of "generationally independent
 * inG". Maybe not the best name 🙂 *)
Notation genIndInG Σ Ω A := (transInG Σ Ω A id).

(* Knowledge about the camera [A] and the fact that there is no associated. *)
Class noTransInG Σ (Ω : gTransformations Σ) (A : cmra) := {
  noTransInG_inG :> inG Σ A;
  noTransInG_trans_lookup : Ω.(gT_map) noTransInG_inG.(inG_id) = None
}.

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
    `{!CmraMorphism t2} `{!transInG Σ Ω A2 t2} γ (a : A2) :
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
    `{!CmraMorphism t2} `{!transInG Σ Ω A2 t2} γ (a : A2) :
      IntoPnextgen _ _ _ :=
    transmap_own_insert_other t1 γ a.

  #[global]
  Instance into_pnextgen_insert_other_ind {A1 A2}
    `{i : noTransInG Σ Ω A1} (t1 : A1 → A1) `{!CmraMorphism t1}
    `{!genIndInG Σ Ω A2} γ (a : A2) :
      IntoPnextgen _ _ (own γ a) :=
    transmap_own_insert_other t1 γ a.

  Lemma transmap_own_insert {A}
    `{i : noTransInG Σ Ω A} (t : A → A) `{!CmraMorphism t} γ (a : A) :
    own γ a ⊢ ⚡={transmap_insert_inG t Ω}=> own γ (t a).
  Proof.
    iIntros "O".
    iApply transmap_own_lookup_Some; last done.
    unfold transmap_insert_inG. simpl.
    rewrite transmap_insert_lookup_eq.
    done.
  Qed.

  Lemma bnextgen_extensional_eq_iprop {Σ} P (f g : iResUR Σ -> iResUR Σ) `{!CmraMorphism f} `{!CmraMorphism g} :
    (forall x i0, f x i0 = g x i0) ->
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
  
  Lemma transmap_insert_extensional_eq {A} `{i : noTransInG Σ Ω A} (t : A → A) (g : A -> A) (C1 : CmraMorphism t) (C2 : CmraMorphism g) P :
    (forall (x : A), t x = g x) ->
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

  #[global]
  Instance into_pnextgen_own_insert {A}
      `{i : noTransInG Σ Ω A} (t : A → A) `{!CmraMorphism t} γ (a : A) :
      IntoPnextgen _ _ _ :=
    transmap_own_insert t γ a.

End nextgen_instances.

Section test.
  Context `{noTransInG Σ Ω A}.
  Context (t : A → A) `{!CmraMorphism t}.
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
