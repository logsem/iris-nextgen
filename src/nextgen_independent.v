From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.algebra Require Import gmap_view.
From iris.prelude Require Import options.

From nextgen Require Import cmra_morphism_extra gen_trans pick.
From nextgen Require Import nextgen_pointwise gmap_view_transformation nextgen_basic utils.
Import uPred.

(** * Independence modality *)

(* The next-gen independence modality. *)
(* Defined on top of the nextgen base logic *)
Local Definition uPred_bnextgen_ind_def {M : ucmra} {C : Type} (R : relation C)
  (pick : C -> M -> M) `{!∀ c, GenTrans (pick c)} (c : C) (P : uPred M) : uPred M := (P ∧ (∀ c', ⌜rc R c c'⌝ → ⚡={ pick c' }=> P)).

Local Definition uPred_bnextgen_ind_aux : seal (@uPred_bnextgen_ind_def).
Proof. by eexists. Qed.

Definition uPred_bnextgen_ind {M : ucmra} {C : Type} R pick {g} c :=
  uPred_bnextgen_ind_aux.(unseal) M C R pick g c.

Local Definition uPred_bnextgen_ind_unseal :
  @uPred_bnextgen_ind = @uPred_bnextgen_ind_def := uPred_bnextgen_ind_aux.(seal_eq).

Notation "⚡◻{ ( R , pick ) ↑ c } P" := (uPred_bnextgen_ind R pick c P)
                            (at level 99, c at level 50, P at level 200, format "⚡◻{ ( R , pick )  ↑  c }  P") : bi_scope.

Section bnextgen_ind_rules.
  Context {M : ucmra} {C : Type} (R : relation C) (pick : C -> M → M)
    `{!∀ c, GenTrans (pick c)}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  (* Ltac unseal := try uPred.unseal; try rewrite !nextgen_basic.uPred_bnextgen_unseal; rewrite !uPred_bnextgen_ind_unseal !/uPred_holds /=. *)
  Ltac unseal := rewrite !uPred_bnextgen_ind_unseal /= /uPred_bnextgen_ind_def.

  Lemma bnextgen_ind_elim c P :
    (⚡◻{ (R,pick) ↑ c } P) ⊢ P.
  Proof.
    unseal.
    iIntros "HP". rewrite and_elim_l. auto.
  Qed.

  Lemma bnextgen_ind_mono P Q c :
    (P ⊢ Q) ->
    (⚡◻{ (R,pick) ↑ c } P) ⊢ ⚡◻{ (R,pick) ↑ c } Q.
  Proof.
    unseal.
    iIntros (HP) "HP".
    iSplit.
    - rewrite and_elim_l HP//.
    - rewrite and_elim_r.
      iIntros (c' Hc).
      iSpecialize ("HP" $! c' Hc).
      iApply (bnextgen_mono with "HP");auto.
  Qed.

  Lemma bnextgen_ind_weaken `{!Transitive R} c' c P :
    rc R c c' ->
    (⚡◻{ (R,pick) ↑ c } P) ⊢ (⚡◻{ (R,pick) ↑ c' } P).
  Proof.
    unseal.
    iIntros (Hc) "HP".
    iSplit;[rewrite and_elim_l//|].
    rewrite and_elim_r.
    iIntros (c'' Hc').
    iSpecialize ("HP" $! c'' with "[%]");[etrans;eauto|].
    auto.
  Qed.

  Lemma bnextgen_ind_bnextgen `{!∀ c1 c2, Decision (R c1 c2)} `{!Trichotomy R}
    `{Hidemp: !∀ c, Idemp (≡) (pick c)}
    `{compose_R_cond: !∀ c1 c2 x, R c1 c2 -> pick c2 (pick c1 x) ≡ pick c1 x }
    `{compose_commute: !∀ c1 c2 x, pick c1 (pick c2 x) ≡ pick c2 (pick c1 x) }
    P c c' :
    rc R c c' ->
    (⚡◻{ (R,pick) ↑ c } P) ⊢ ⚡={ pick c' }=> ⚡◻{ (R,pick) ↑ c } P.
  Proof.
    unseal. 
    iIntros (Hc) "HP".
    rewrite -bnextgen_and.
    iSplit.
    - rewrite and_elim_r.
      iSpecialize ("HP" $! c' Hc). auto.
    - iApply bnextgen_forall. iIntros (c'').
      rewrite bnextgen_impl_plain.
      iIntros (Hc').
      rewrite bnextgen_compose and_elim_r.
      pose proof (Trichotomy0 c' c'') as Hcases.
      destruct Hcases as [Hc''|[->|Hc'']].
      + iSpecialize ("HP" $! c' Hc).
        iApply bnextgen_extensional_equiv;[|iFrame].
        intros;simpl. rewrite compose_R_cond;auto.
      + iSpecialize ("HP" $! c'' Hc).
        iApply bnextgen_extensional_equiv;[|iFrame].
        intros;simpl. rewrite Hidemp. auto.
      + iSpecialize ("HP" $! c'' Hc').
        iApply bnextgen_extensional_equiv;[|iFrame].
        intros;simpl. rewrite compose_commute compose_R_cond;auto.
  Qed.

  Lemma bnextgen_ind_intro P c :
    (∀ c', rc R c c' -> P ⊢ ⚡={ pick c' }=> P) ->
    P ⊢ ⚡◻{ (R,pick) ↑ c } P.
  Proof.
    unseal.
    iIntros (Hcond) "HP".
    iSplit;auto.
    iIntros (c' Hc).
    rewrite {1}Hcond;eauto.
  Qed.
          
  Lemma bnextgen_ind_plainly P c :
    ■ P ⊢ ⚡◻{ (R,pick) ↑ c } ■ P.
  Proof.
    unseal.
    iIntros "#HP". iSplit;auto.
    iIntros (c' Hc).
    by iApply bnextgen_intro_plainly.
  Qed.

  Lemma bnextgen_ind_from_plainly P c :
    ■ P ⊢ (⚡◻{ (R,pick) ↑ c } P).
  Proof.
    iIntros "HP".
    iDestruct (bnextgen_ind_plainly with "HP") as "HP".
    iApply (bnextgen_ind_mono with "HP").
    iIntros "#HP".
    iDestruct (plainly_elim with "HP") as "$".
  Qed.

  Lemma bnextgen_ind_and P Q c :
    (⚡◻{ (R,pick) ↑ c } P) ∧ (⚡◻{ (R,pick) ↑ c } Q) ⊢ ⚡◻{ (R,pick) ↑ c } P ∧ Q.
  Proof.
    unseal.
    iIntros "HP".
    iSplit.
    - iSplit;[rewrite !and_elim_l//|rewrite and_elim_r and_elim_l//].
    - iIntros (c' Hc).
      rewrite -bnextgen_and.
      iSplit.
      + rewrite and_elim_l and_elim_r.
        iApply "HP". auto.
      + rewrite !and_elim_r.
        iApply "HP";auto.
  Qed.
    
  Lemma bnextgen_ind_forall {A : Type} (P : A -> uPred M) c :
    (∀ x, ⚡◻{ (R,pick) ↑ c } P x) ⊢ ⚡◻{ (R,pick) ↑ c } ∀ x, P x.
  Proof.
    unseal.
    iIntros "HP".
    iSplit.
    - iIntros (x).
      iSpecialize ("HP" $! x).
      rewrite and_elim_l;auto.
    - iIntros (c' Hc).
      iApply bnextgen_forall. iIntros (x).
      iSpecialize ("HP" $! x).
      rewrite and_elim_r.
      iApply "HP";auto.
  Qed.

  Lemma bnextgen_ind_later (P : uPred M) c :
    (▷ ⚡◻{ (R,pick) ↑ c } P) ⊣⊢ (⚡◻{ (R,pick) ↑ c } ▷ P).
  Proof.
    unseal.
    iSplit; iIntros "HP".
    - iSplit;[rewrite and_elim_l//|].
      iIntros (c' Hc). iApply bnextgen_later.
      rewrite and_elim_r. iNext.
      iApply "HP";auto.
    - iSplit;[rewrite and_elim_l//|].
      rewrite and_elim_r.
      iIntros (c' Hc). iApply bnextgen_later.
      iApply "HP";auto.
  Qed.

  Lemma bnextgen_ind_idemp (P : uPred M) c
    `{!∀ c1 c2, Decision (R c1 c2)} `{!Trichotomy R}
    `{Hidemp: !∀ c, Idemp (≡) (pick c)}
    `{compose_R_cond: !∀ c1 c2 x, R c1 c2 -> pick c2 (pick c1 x) ≡ pick c1 x }
    `{compose_commute: !∀ c1 c2 x, pick c1 (pick c2 x) ≡ pick c2 (pick c1 x) } :
    (⚡◻{ (R,pick) ↑ c } P) ⊣⊢ (⚡◻{ (R,pick) ↑ c } ⚡◻{ (R,pick) ↑ c } P).
  Proof.
    unseal.
    iSplit.
    - iIntros "HP".
      iSplit;auto.
      iIntros (c' Hc).
      rewrite {1}and_elim_r.
      iApply bnextgen_and.
      iSplit;[iApply "HP";auto|].
      rewrite bnextgen_forall.
      iIntros (c'').
      rewrite bnextgen_impl_plain.
      iIntros (Hc').
      iApply bnextgen_compose.
      pose proof (Trichotomy0 c' c'') as Hcases.
      destruct Hcases as [Hc''|[->|Hc'']].
      + iSpecialize ("HP" $! c' Hc).
        iApply bnextgen_extensional_equiv;[|iFrame].
        intros;simpl. rewrite compose_R_cond;auto.
      + iSpecialize ("HP" $! c'' Hc).
        iApply bnextgen_extensional_equiv;[|iFrame].
        intros;simpl. rewrite Hidemp. auto.
      + iSpecialize ("HP" $! c'' Hc').
        iApply bnextgen_extensional_equiv;[|iFrame].
        intros;simpl. rewrite compose_commute compose_R_cond;auto.
    - iIntros "HP".
      rewrite and_elim_l. auto.
  Qed.

  Global Instance bnextgen_ind_mono' c :
    Proper ((⊢) ==> (⊢)) (uPred_bnextgen_ind R pick c).
  Proof. intros P Q. apply bnextgen_ind_mono. Qed.

  Global Instance bnextgen_ind_ne c :
    NonExpansive (uPred_bnextgen_ind R pick c).
  Proof.
    intros ??? Hne.
    unseal. f_equiv;auto.
    apply forall_ne;rewrite /pointwise_relation=>a.
    apply impl_ne;auto.
    f_equiv. auto.
  Qed.

  Global Instance bnextgen_ind_proper c :
    Proper ((≡) ==> (≡)) (uPred_bnextgen_ind R pick c) := ne_proper _.
    
End bnextgen_ind_rules.

Section bnextgen_ind_rules.
  Context {M : ucmra} {C : Type} (R : relation C) (pick : C -> M → M)
    `{!∀ c, CmraMorphism (pick c)}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := rewrite !uPred_bnextgen_ind_unseal /= /uPred_bnextgen_ind_def.

  Global Instance bnextgen_ind_mod_persistent P c : Persistent P -> Persistent (⚡◻{ (R,pick) ↑ c } P).
  Proof. unseal. apply _. Qed.

  Lemma bnextgen_ind_always (P : uPred M) c :
    (□ ⚡◻{ (R,pick) ↑ c } P) ⊣⊢ (⚡◻{ (R,pick) ↑ c } □ P).
  Proof.
    unseal.
    iSplit.
    - iIntros "#HP".
      iSplit.
      + rewrite and_elim_l//.
      + rewrite and_elim_r.
        iIntros (c' Hc).
        iApply bnextgen_persistently.
        iModIntro. iApply "HP";auto.
    - iIntros "HP". rewrite intuitionistically_and.
      iSplit.
      + rewrite and_elim_l//.
      + rewrite and_elim_r.
        iIntros (c' Hc).
        iSpecialize ("HP" $! c' Hc).
        by iApply bnextgen_persistently.
  Qed.

  Lemma bnextgen_ind_sep P Q c :
    (⚡◻{ (R,pick) ↑ c } P) ∗ (⚡◻{ (R,pick) ↑ c } Q) ⊢ ⚡◻{ (R,pick) ↑ c } P ∗ Q.
  Proof.
    unseal.
    iIntros "[HP HQ]".
    iSplit;[rewrite !and_elim_l;iFrame|].
    rewrite !and_elim_r.
    iIntros (c' Hc).
    iSpecialize ("HP" $! c' Hc).
    iSpecialize ("HQ" $! c' Hc).
    iModIntro. iFrame.
  Qed.

  Lemma bnextgen_ind_wand_plainly (P Q : uPred M) c :
    (⚡◻{ (R,pick) ↑ c } ■ P -∗ Q) ⊣⊢ (■ P -∗ ⚡◻{ (R,pick) ↑ c } Q).
  Proof.
    unseal.
    iSplit.
    - iIntros "HP".
      iIntros "#HP'".
      iSplit.
      + rewrite and_elim_l.
        iApply "HP";auto.
      + iIntros (c' Hc). rewrite and_elim_r.
        iSpecialize ("HP" $! c' Hc).
        iModIntro. iApply "HP";auto.
    - iIntros "HP". iSplit.
      + iIntros "#HP'".
        iSpecialize ("HP" with "HP'").
        rewrite and_elim_l//.
      + iIntros (c' Hc).
        iApply bnextgen_wand_plainly.
        iIntros "HP'".
        iSpecialize ("HP" with "HP'").
        rewrite and_elim_r.
        iApply "HP";auto.
  Qed.

  Lemma bnextgen_ind_impl (P Q : uPred M) c :
    (⚡◻{ (R,pick) ↑ c } ■ P → Q) ⊣⊢ (■ P → ⚡◻{ (R,pick) ↑ c } Q).
  Proof.
    rewrite !impl_wand_plainly. iApply bnextgen_ind_wand_plainly.
  Qed.
  
End bnextgen_ind_rules.


(** * Class for iProps that are independent from a specific nextgen transformation *)

Class GenIndependent {M : ucmra} {C : Type} (R : relation C) (pick : C -> M -> M) `{!∀ c, GenTrans (pick c)} (c : C) (P : uPred M) := gen_independent : ∀ c', rc R c c' -> P ⊢ ⚡={ pick c' }=> P.
Global Arguments GenIndependent {_ _} _ _ {_} _ _%I : simpl never.
Global Arguments gen_independent {_ _} _ _ {_} _ _%I {_}.
Global Hint Mode GenIndependent + + + + ! ! ! : typeclass_instances.
Global Instance: Params (@GenIndependent) 4 := {}.

Section gen_independent_instances.
  Context {M : ucmra} {C : Type} (R : relation C) (f : C -> M -> M) (c : C).
  
  Global Instance pure_gen_independent `{!∀ c, GenTrans (f c)} φ : GenIndependent R f c ⌜φ⌝.
  Proof. iIntros (c' Hc'). rewrite -plainly_pure. apply bnextgen_intro_plainly. Qed.

  Global Instance emp_gen_independent `{!∀ c, GenTrans (f c)} : GenIndependent R f c emp.
  Proof. iIntros (c' Hc'). rewrite -plainly_emp. apply bnextgen_intro_plainly. Qed.

  Global Instance plain_gen_independent `{!∀ c, GenTrans (f c)} P : Plain P -> Absorbing P -> GenIndependent R f c P.
  Proof. iIntros (HP HA c' Hc'). by apply bnextgen_intro_plain. Qed.

  Global Instance gen_ind_mod_gen_independent `{!∀ c, GenTrans (f c)}
                  `{∀ c1 c2 : C, Decision (R c1 c2)}
                  `{!Trichotomy R} `{!∀ c, Idemp (≡) (f c)}
                  `{∀ (c1 c2 : C) (x : M), R c1 c2 → f c2 (f c1 x) ≡ f c1 x}
                  `{∀ (c1 c2 : C) (x : M), f c1 (f c2 x) ≡ f c2 (f c1 x)} P
    : GenIndependent R f c (⚡◻{ (R,f) ↑ c } P).
  Proof. iIntros (c' Hc'). apply bnextgen_ind_bnextgen;auto. Qed.

  Global Instance and_gen_independent `{!∀ c, GenTrans (f c)} P Q :
    GenIndependent R f c P -> GenIndependent R f c Q -> GenIndependent R f c (P ∧ Q).
  Proof.
    rewrite /GenIndependent.
    intros Hp1 Hp2 c' Hcr.
    rewrite -bnextgen_and -(Hp1 c' Hcr) -(Hp2 c' Hcr)//.
  Qed.

  Global Instance or_gen_independent `{!∀ c, GenTrans (f c)} P Q :
    GenIndependent R f c P -> GenIndependent R f c Q -> GenIndependent R f c (P ∨ Q).
  Proof.
    rewrite /GenIndependent.
    intros Hp1 Hp2 c' Hcr.
    rewrite -bnextgen_or -(Hp1 c' Hcr) -(Hp2 c' Hcr)//.
  Qed.

  Global Instance exist_gen_independent `{!∀ c, GenTrans (f c)} {A : Type} (P : A -> uPred M) :
    (∀ (x : A), GenIndependent R f c (P x)) -> GenIndependent R f c (∃ x, P x).
  Proof.
    rewrite /GenIndependent.
    iIntros (Hp c' Hcr) "(%a & Ha)".
    specialize (Hp a c' Hcr).
    iDestruct (Hp with "[$]") as "Ha".
    rewrite bnextgen_exist. by iExists a.
  Qed.

  Global Instance forall_gen_independent `{!∀ c, GenTrans (f c)} {A : Type} (P : A -> uPred M) :
    (∀ (x : A), GenIndependent R f c (P x)) -> GenIndependent R f c (∀ x, P x).
  Proof.
    rewrite /GenIndependent.
    iIntros (Hp c' Hcr).
    rewrite bnextgen_forall.
    iIntros "H" (a).
    specialize (Hp a c' Hcr). iSpecialize ("H" $! a).
    by iDestruct (Hp with "[$]") as "Ha".
  Qed.

  Global Instance sep_gen_independent `{morph: !∀ c, CmraMorphism (f c)} P Q :
    GenIndependent R f c P -> GenIndependent R f c Q -> GenIndependent R f c (P ∗ Q).
  Proof.
    rewrite /GenIndependent.
    iIntros (Ha Hb c' Hcr) "[Hp Hq]".
    iDestruct (Ha with "[$]") as "H1";eauto.
    iDestruct (Hb with "[$]") as "H2";eauto.
    iApply bnextgen_sep_2. iFrame.
  Qed.

  Global Instance from_option_gen_independent `{!∀ c, GenTrans (f c)} {A : Type} (P : uPred M) (Ψ : A -> uPred M) (mx : option A) :
    (∀ (x : A), GenIndependent R f c (Ψ x)) -> GenIndependent R f c P -> GenIndependent R f c (from_option Ψ P mx).
  Proof.
    rewrite /GenIndependent.
    destruct mx;simpl;iIntros (Ha Hb c' Hcr) "H".
    - by rewrite -Ha.
    - by rewrite -Hb.
  Qed.

  Lemma gen_ind_intro `{!∀ c, GenTrans (f c)} P c' :
    GenIndependent R f c P ->
    rc R c c' ->
    P ⊢ ⚡={ f c' }=> P.
  Proof.
    intros Hind Hrc.
    rewrite /GenIndependent in Hind.
    by iApply Hind.
  Qed.
    
    
End gen_independent_instances.

(** * Class for iProps that are independent by an Ω <- (f1,f2) transformation *)

(* Notation GenIndependent2Ω Ω c P := (GenIndependent CR (λ c, build_trans ((transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω).(gT_map))) c P). *)

Notation "⚡={ M }=> P" := (nextgen_omega M P)
                            (at level 99, M at level 50, P at level 200, format "⚡={ M }=>  P") : bi_scope.

Local Existing Instances noTransInG_A_inG noTransInG_B_inG noTransInG_inG.

Definition bnextgen_bounded_ind {Σ : gFunctors} {A : cmra} {pick : pick_transform_rel A}
  (Ω : gTransformations Σ) `{!noTwoTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) A} (c : C) (P : iProp Σ) : iProp Σ :=
  ⚡◻{ (CR,λ c, build_trans (gT_map (transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω))) ↑ c} P.

Notation "⚡◻{ Ω ↑ c } P" := (bnextgen_bounded_ind Ω c P)
                               (at level 99, Ω at level 50, c at level 20, P at level 200, format "⚡◻{ Ω  ↑  c }  P") : bi_scope.

Class IntoInextgen {Σ : gFunctors} {A : cmra} {pick : pick_transform_rel A}
  (Ω : gTransformations Σ) `{!noTwoTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) A} (c : C) (P : iProp Σ) (Q : iProp Σ) :=
  into_inextgen : P ⊢ ⚡◻{ Ω ↑ c } Q.
Global Hint Mode IntoInextgen + + + + ! ! - - : typeclass_instances.

Section bnextgen_bounded_ind_rules.
  Context {Σ : gFunctors} {A : cmra} {pick : pick_transform_rel A}
    `{!noTwoTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) A}.

  Lemma bnextgen_bounded_ind_elim P c :
    (⚡◻{ Ω ↑ c } P) ⊢ P.
  Proof.
    iIntros "Hb".
    iDestruct (bnextgen_ind_elim with "Hb") as "$".
  Qed.

  Lemma bnextgen_bounded_ind_bnextgen_intro P c c' :
    rc CR c c' ->
    (⚡◻{ Ω ↑ c } P) ⊢ ⚡={transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω}=> ⚡◻{ Ω ↑ c } P.
  Proof.
    iIntros (Hcr) "Hb".
    rewrite /bnextgen_bounded_ind.
    iDestruct (bnextgen_ind_bnextgen with "Hb") as "Hb";[eauto..|].
    { apply C_total. }
    { intros c0 x.
      apply equiv_dist. intros n. simpl.
      erewrite <-build_trans_two_insert_compose;try apply _.
      intros i0.
      apply build_trans_two_insert_extensional_eq;try apply _.
      - apply idemp_pick_transform.
      - apply C_pick_idemp. }
    { intros c1 c2 x Hcr'.
      apply equiv_dist. intros n. simpl.
      erewrite <-build_trans_two_insert_compose;try apply _.
      intros i0.
      apply build_trans_two_insert_extensional_eq;try apply _.
      - apply inv_pick_transform_compose_left. by constructor.
      - intros x0. rewrite /= C_indep C_comp//. }
    { intros c1 c2 x.
      apply equiv_dist. intros n. simpl.
      erewrite <-build_trans_two_insert_compose;try apply _.
      erewrite <-build_trans_two_insert_compose;try apply _.
      intros i0.
      apply build_trans_two_insert_extensional_eq;try apply _.
      - intros x0. simpl. rewrite indep_pick_transform//.
      - apply C_indep. }
    iModIntro. iFrame.
  Qed.

  Lemma bnextgen_bounded_ind_idemp P c :
    (⚡◻{ Ω ↑ c } P) ⊣⊢ (⚡◻{ Ω ↑ c } ⚡◻{ Ω ↑ c } P).
  Proof.
    rewrite /bnextgen_bounded_ind.
    iApply bnextgen_ind_idemp.
    { apply C_total. }
    { intros c0 x.
      apply equiv_dist. intros n. simpl.
      erewrite <-build_trans_two_insert_compose;try apply _.
      intros i0.
      apply build_trans_two_insert_extensional_eq;try apply _.
      - apply idemp_pick_transform.
      - apply C_pick_idemp. }
    { intros c1 c2 x Hcr'.
      apply equiv_dist. intros n. simpl.
      erewrite <-build_trans_two_insert_compose;try apply _.
      intros i0.
      apply build_trans_two_insert_extensional_eq;try apply _.
      - apply inv_pick_transform_compose_left. by constructor.
      - intros x0. rewrite /= C_indep C_comp//. }
    { intros c1 c2 x.
      apply equiv_dist. intros n. simpl.
      erewrite <-build_trans_two_insert_compose;try apply _.
      erewrite <-build_trans_two_insert_compose;try apply _.
      intros i0.
      apply build_trans_two_insert_extensional_eq;try apply _.
      - intros x0. simpl. rewrite indep_pick_transform//.
      - apply C_indep. }
  Qed.

  Lemma bnextgen_bounded_ind_later P c :
    (▷ ⚡◻{ Ω ↑ c } P) ⊣⊢ (⚡◻{ Ω ↑ c } ▷ P).
  Proof.
    apply bnextgen_ind_later.
  Qed.

  Lemma bnextgen_bounded_ind_always P c :
    (□ ⚡◻{ Ω ↑ c } P) ⊣⊢ (⚡◻{ Ω ↑ c } □ P).
  Proof.
    apply bnextgen_ind_always.
  Qed.

  Lemma bnextgen_bounded_ind_sep P Q c :
    (⚡◻{ Ω ↑ c } P) ∗ (⚡◻{ Ω ↑ c } Q) ⊢ (⚡◻{ Ω ↑ c } P ∗ Q).
  Proof.
    apply bnextgen_ind_sep.
  Qed.

  Lemma bnextgen_bounded_ind_and P Q c :
    (⚡◻{ Ω ↑ c } P) ∧ (⚡◻{ Ω ↑ c } Q) ⊢ (⚡◻{ Ω ↑ c } P ∧ Q).
  Proof.
    apply bnextgen_ind_and.
  Qed.

  Lemma bnextgen_bounded_ind_forall {B : Type} (P : B -> iProp Σ) c :
    (∀ x, ⚡◻{ Ω ↑ c } P x) ⊢ ⚡◻{ Ω ↑ c } ∀ x, P x.
  Proof.
    apply bnextgen_ind_forall.
  Qed.

  Lemma bnextgen_bounded_ind_wand_plainly (P Q : iProp Σ) c :
    (⚡◻{ Ω ↑ c }  ■ P -∗ Q) ⊣⊢ (■ P -∗ ⚡◻{ Ω ↑ c } Q).
  Proof.
    iApply bnextgen_ind_wand_plainly.
  Qed.

  Lemma bnextgen_bounded_ind_impl (P Q : iProp Σ) c :
    (⚡◻{ Ω ↑ c } ■ P → Q) ⊣⊢ (■ P → ⚡◻{ Ω ↑ c } Q).
  Proof.
    iApply bnextgen_ind_impl.
  Qed.

  Lemma bnextgen_bounded_ind_if_always P c b :
    (□?b ⚡◻{ Ω ↑ c } P) ⊣⊢ (⚡◻{ Ω ↑ c } □?b P).
  Proof.
    destruct b;simpl.
    - apply bnextgen_ind_always.
    - auto. 
  Qed.

  Lemma bnextgen_bounded_ind_weaken c' c P :
    rc CR c c' ->
    (⚡◻{ Ω ↑ c } P) ⊢ (⚡◻{ Ω ↑ c' } P).
  Proof.
    intros Hcr.
    apply bnextgen_ind_weaken;auto.
    apply _.
  Qed.

  Lemma bnextgen_bounded_ind_weaken_once c' c P :
    rc CR c c' ->
    (⚡◻{ Ω ↑ c } P) ⊢ (⚡◻{ Ω ↑ c' } ⚡◻{ Ω ↑ c } P).
  Proof.
    iIntros (Hcr) "Hc".
    rewrite {1}bnextgen_bounded_ind_idemp.
    iDestruct (bnextgen_bounded_ind_weaken with "Hc") as "$";eauto.
  Qed.

  Lemma bnextgen_bounded_ind_GenIndependent_intro P c :
    (∀ c', rc CR c c' -> P ⊢ ⚡={ transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω }=> P) ->
    P ⊢ ⚡◻{ Ω ↑ c } P.
  Proof.
    iIntros (HP) "HP".
    iApply bnextgen_ind_intro;auto.
  Qed.

  Lemma modality_bnextgen_bounded_ind_mixin c :
    modality_mixin (bnextgen_bounded_ind Ω c)
      (MIEnvTransform (IntoInextgen Ω c)) (MIEnvTransform (IntoInextgen Ω c)).
  Proof.
    split; simpl; split_and?.
    - intros ?? Hi.
      rewrite Hi.
      rewrite bnextgen_bounded_ind_always.
      auto.
    - intros. rewrite bnextgen_ind_and. auto.
    - done.
    - iIntros "_". iApply bnextgen_ind_from_plainly;auto.
    - intros. apply bnextgen_ind_mono;auto.
    - intros. apply bnextgen_bounded_ind_sep.
  Qed.
  Definition modality_inextgen c :=
    Modality _ (modality_bnextgen_bounded_ind_mixin c).

  Global Instance from_modal_inextgen P c :
    FromModal True (modality_inextgen c) (⚡◻{ Ω ↑ c } P) (⚡◻{ Ω ↑ c } P) P | 1.
  Proof. by rewrite /FromModal. Qed.

  Global Instance into_inextgen_mono P c :
    IntoInextgen Ω c (⚡◻{ Ω ↑ c } P) (⚡◻{ Ω ↑ c } P).
  Proof. rewrite /IntoInextgen. iIntros "HP".
         rewrite -bnextgen_bounded_ind_idemp. auto. Qed.

  Global Instance into_inextgen_plain P c `{!Plain P} :
    IntoInextgen Ω c P P.
  Proof. rewrite /IntoInextgen. iIntros "HP".
         iDestruct (plain_plainly_2 with "HP") as "HP".
         by iApply bnextgen_ind_from_plainly. Qed.

  Global Instance into_inextgen_and P P' Q Q' c :
    IntoInextgen Ω c P P' →
    IntoInextgen Ω c Q Q' →
    IntoInextgen Ω c (P ∧ Q) (P' ∧ Q').
  Proof. rewrite /IntoInextgen. iIntros (HP HQ) "HP".
         rewrite HP HQ. iApply bnextgen_ind_and;auto. Qed.

  Global Instance into_inextgen_sep P P' Q Q' c :
    IntoInextgen Ω c P P' →
    IntoInextgen Ω c Q Q' →
    IntoInextgen Ω c (P ∗ Q) (P' ∗ Q').
  Proof. rewrite /IntoInextgen. iIntros (HP HQ) "HP".
         rewrite HP HQ. iApply bnextgen_ind_sep;auto. Qed.

  Global Instance into_inextgen_later P P' c :
    IntoInextgen Ω c P P' ->
    IntoInextgen Ω c (▷ P) (▷ P').
  Proof. rewrite /IntoInextgen. iIntros (HP) "HP".
         rewrite -bnextgen_bounded_ind_later. iNext.
         by rewrite HP. Qed.

  Global Instance into_inextgen_forall {B : Type} (Ψ Ψ' : B -> iProp Σ) c :
    (∀ x, IntoInextgen Ω c (Ψ x) (Ψ' x)) → IntoInextgen Ω c (∀ x, Ψ x) (∀ x, Ψ' x).
  Proof. rewrite /IntoInextgen. iIntros (HP) "HP".
         rewrite -bnextgen_bounded_ind_forall. iIntros (x).
         iSpecialize ("HP" $! x). by rewrite HP. Qed.

  Global Instance into_inextgen_exists {B : Type} (Ψ Ψ' : B -> iProp Σ) c :
    (∀ x, IntoInextgen Ω c (Ψ x) (Ψ' x)) → IntoInextgen Ω c (∃ x, Ψ x) (∃ x, Ψ' x).
  Proof. rewrite /IntoInextgen. iIntros (HP) "(%x & HP)".
         rewrite HP. iApply (bnextgen_ind_mono with "HP");iIntros "HP".
         iExists x. auto. Qed.

  Global Instance into_inextgen_wand_plain P `{!Plain P} Q Q' c :
      IntoInextgen Ω c Q Q' → IntoInextgen Ω c (P -∗ Q) (P -∗ Q').
  Proof.
    rewrite /IntoInextgen. iIntros (HQ) "HP".
    rewrite HQ.
    rewrite -{1}(plain_plainly P).
    iDestruct (bnextgen_bounded_ind_wand_plainly with "HP") as "HP".
    iApply (bnextgen_ind_mono with "HP");iIntros "HP".
    by rewrite plain_plainly.
  Qed.

  Global Instance into_inextgen_impl_plain P `{!Plain P} Q Q' c :
      IntoInextgen Ω c Q Q' → IntoInextgen Ω c (P → Q) (P → Q').
  Proof.
    rewrite /IntoInextgen. iIntros (HQ) "HP".
    rewrite HQ.
    rewrite -{1}(plain_plainly P).
    iDestruct (bnextgen_bounded_ind_impl with "HP") as "HP".
    iApply (bnextgen_ind_mono with "HP");iIntros "HP".
    by rewrite plain_plainly.
  Qed.
  
End bnextgen_bounded_ind_rules.

Notation GenIndependent2Ω Ω c P := (IntoInextgen Ω c P P).

Section bnextgen_bounded_ind_rules.
  Context {Σ : gFunctors} {A : cmra} {pick : pick_transform_rel A}
    `{!noTwoTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) A}.

  Lemma gen_ind_insert2_intro P c c' :
    GenIndependent2Ω Ω c P ->
    rc CR c c' ->
    P ⊢ ⚡={transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω}=> P.
  Proof.
    rewrite /IntoInextgen.
    intros Hind Hcr.
    iIntros "HP". iDestruct (Hind with "HP") as "HP".
    iDestruct (bnextgen_bounded_ind_bnextgen_intro with "HP") as "HP";[eauto|].
    iModIntro. iDestruct (bnextgen_bounded_ind_elim with "HP") as "$".
  Qed.

End bnextgen_bounded_ind_rules.
