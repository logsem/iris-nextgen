From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.algebra Require Import gmap_view.
From iris.prelude Require Import options.

From nextgen Require Import cmra_morphism_extra gen_trans pick.
From nextgen Require Import nextgen_pointwise gmap_view_transformation nextgen_basic utils.
Import uPred.

(** * Independence modality *)

(** When working in the model, it is convenient to be able to treat [uPred] as
[nat → M → Prop]. But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.

(* The next-gen independence modality. *)
Local Program Definition uPred_bnextgen_ind_def {M : ucmra}
  {C : Type} (R : relation C) (pick : C -> M -> M)
  `{!∀ c, GenTrans (pick c)} (c : C) (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ ((* ∀ n x, ✓{n} x -> P n x -> *) ∀ c', rc R c c' -> P n (pick c' x)) |}.
Next Obligation.
  intros ???????????[HP Hiff]??.
  specialize (gen_trans_monoN (pick c) n2) as monoN.
  split; [naive_solver eauto using uPred_mono, monoN|].
  intros c' Hc'.
  eapply uPred_mono;[by apply Hiff|auto..].
  apply gen_trans_monoN;auto.
  (* eapply Hiff;eauto. *) (* ;[etrans;eauto|]. *)
  (* eapply cmra_includedN_le in H0;eauto. etrans;eauto. *)
Qed.

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

  Ltac unseal := try uPred.unseal; try rewrite !nextgen_basic.uPred_bnextgen_unseal; rewrite !uPred_bnextgen_ind_unseal !/uPred_holds /=.

  Lemma bnextgen_ind_elim c P :
    (⚡◻{ (R,pick) ↑ c } P) ⊢ P.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def.
    by split;intros ???[HP Hcond].
  Qed.

  Lemma bnextgen_ind_mono P Q c :
    (P ⊢ Q) ->
    (⚡◻{ (R,pick) ↑ c } P) ⊢ ⚡◻{ (R,pick) ↑ c } Q.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def /nextgen_basic.uPred_bnextgen_def.
    split; simpl; intros ???[HP Hcond].
    apply H0 in HP as HQ;auto.
    split;auto.
    intros c' Hc'. apply H0;eauto.
    by apply gen_trans_validN.
  Qed.

  Lemma bnextgen_ind_bnextgen `{!∀ c1 c2, Decision (R c1 c2)} `{!Trichotomy R}
    `{Hidemp: !∀ c, Idemp (≡) (pick c)}
    `{compose_R_cond: !∀ c1 c2 x, R c1 c2 -> pick c2 (pick c1 x) ≡ pick c1 x }
    `{compose_commute: !∀ c1 c2 x, pick c1 (pick c2 x) ≡ pick c2 (pick c1 x) }
    P c c' :
    rc R c c' ->
    (⚡◻{ (R,pick) ↑ c } P) ⊢ ⚡={ pick c' }=> ⚡◻{ (R,pick) ↑ c } P.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def /nextgen_basic.uPred_bnextgen_def.
    split; simpl; intros ???[HP Hcond].
    split;auto. intros c'' Hc''.
    pose proof (Trichotomy0 c' c'') as Hcases.
    destruct Hcases as [Hc|[->|Hc]].
    - rewrite compose_R_cond;auto.
    - rewrite Hidemp. auto.
    - rewrite compose_commute compose_R_cond;auto.
  Qed.

  Lemma bnextgen_ind_intro P c :
    (∀ c', rc R c c' -> P ⊢ ⚡={ pick c' }=> P) ->
    P ⊢ ⚡◻{ (R,pick) ↑ c } P.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def /nextgen_basic.uPred_bnextgen_def.
    split;simpl;intros ??? HP.
    split;auto.
    intros c' Hrc.
    apply H0 in Hrc. apply Hrc;auto.
  Qed.
          
  Lemma bnextgen_ind_plainly P c :
    ■ P ⊢ ⚡◻{ (R,pick) ↑ c } ■ P.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def /nextgen_basic.uPred_bnextgen_def.
    split;simpl;intros ??? HP.
    split;auto.
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
    unseal. rewrite /uPred_bnextgen_ind_def /nextgen_basic.uPred_bnextgen_def.
    split;simpl; intros ??? [[HP HPc][HQ HQc]].
    split;auto.
  Qed.
    
  Lemma bnextgen_ind_forall {A : Type} (P : A -> uPred M) c :
    (∀ x, ⚡◻{ (R,pick) ↑ c } P x) ⊢ ⚡◻{ (R,pick) ↑ c } ∀ x, P x.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def.
    split;simpl;intros ??? HP.
    split;[intros a;naive_solver|].
    intros c' Hcr a'. naive_solver.
  Qed.

  Lemma bnextgen_ind_later (P : uPred M) c :
    (▷ ⚡◻{ (R,pick) ↑ c } P) ⊣⊢ (⚡◻{ (R,pick) ↑ c } ▷ P).
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def.
    split;simpl;intros ?? HP.
    destruct n;auto. naive_solver.
  Qed.

  Lemma bnextgen_ind_idemp (P : uPred M) c
    `{!∀ c1 c2, Decision (R c1 c2)} `{!Trichotomy R}
    `{Hidemp: !∀ c, Idemp (≡) (pick c)}
    `{compose_R_cond: !∀ c1 c2 x, R c1 c2 -> pick c2 (pick c1 x) ≡ pick c1 x }
    `{compose_commute: !∀ c1 c2 x, pick c1 (pick c2 x) ≡ pick c2 (pick c1 x) } :
    (⚡◻{ (R,pick) ↑ c } P) ⊣⊢ (⚡◻{ (R,pick) ↑ c } ⚡◻{ (R,pick) ↑ c } P).
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def.
    split;simpl;intros ???.
    split;intros [HP Hc].
    - split;auto. intros.
      split;auto. intros.
      pose proof (Trichotomy0 c' c'0) as Hcases.
      destruct Hcases as [Hc'|[->|Hc']].
      + rewrite compose_R_cond;auto.
      + rewrite Hidemp;auto.
      + rewrite compose_commute compose_R_cond;auto.
    - destruct HP as [HP Hc'].
      split;auto.
  Qed.
    
End bnextgen_ind_rules.

Section bnextgen_ind_rules.
  Context {M : ucmra} {C : Type} (R : relation C) (pick : C -> M → M)
    `{!∀ c, CmraMorphism (pick c)}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Local Arguments uPred_holds {_} !_ _ _ /.

  Ltac unseal := try uPred.unseal; try rewrite !nextgen_basic.uPred_bnextgen_unseal; rewrite !uPred_bnextgen_ind_unseal !/uPred_holds /=.

  Global Instance bnextgen_ind_mod_persistent P c : Persistent P -> Persistent (⚡◻{ (R,pick) ↑ c } P).
  Proof.
    rewrite /Persistent.
    unseal.
    rewrite /uPred_bnextgen_ind_def /upred.uPred_persistently_def /=.
    inversion 1. split. simpl in *.
    intros n x Hx [Hp Hcond].
    apply uPred_in_entails in Hp as Hpcore;auto.
    split;auto. intros c' Hc'.
    apply Hcond in Hc' as Hcond'.
    apply uPred_in_entails in Hcond';[|apply gen_trans_validN;auto;apply _].
    pose proof (cmra_morphism_pcore (pick c') x) as Hcore.
    rewrite !cmra_pcore_core in Hcore. simpl in Hcore.
    inversion Hcore;subst. rewrite H3. auto.
  Qed.

  Lemma bnextgen_ind_always (P : uPred M) c :
    (□ ⚡◻{ (R,pick) ↑ c } P) ⊣⊢ (⚡◻{ (R,pick) ↑ c } □ P).
  Proof.
    rewrite /bi_intuitionistically /bi_affinely.
    unseal. rewrite /uPred_bnextgen_ind_def. simpl.
    split;simpl;intros ???.
    split;simpl.
    - intros [?[HP Hc]].
      split;auto. intros c' Hc'.
      pose proof (cmra_morphism_pcore (pick c') x) as Hcore.
      rewrite !cmra_pcore_core in Hcore. simpl in Hcore.
      inversion Hcore;subst. rewrite -H4. auto.
    - intros [[_ HP]Hc].
      do 2 (split;auto). intros c' Hc'.
      pose proof (cmra_morphism_pcore (pick c') x) as Hcore.
      rewrite !cmra_pcore_core in Hcore. simpl in Hcore.
      inversion Hcore;subst. rewrite H3. naive_solver.
  Qed.

  Lemma bnextgen_ind_sep P Q c :
    (⚡◻{ (R,pick) ↑ c } P) ∗ (⚡◻{ (R,pick) ↑ c } Q) ⊢ ⚡◻{ (R,pick) ↑ c } P ∗ Q.
  Proof.
    unseal. rewrite /uPred_bnextgen_ind_def /nextgen_basic.uPred_bnextgen_def.
    split;simpl; intros ??? [x1 [x2 [Heq [[HP HPx] [HQ HQx]]]]].
    split;[naive_solver|].
    (* intros ?? Hx0 [x1' [x2' [Heq' [HP' HQ']]]]. *)
    intros c' Hrc.
    exists (pick c' x1),(pick c' x2). rewrite -cmra_morphism_op.
    rewrite Heq. split;[|naive_solver]. auto.
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

Notation GenIndependent2Ω Ω c P := (GenIndependent CR (λ c, build_trans ((transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω).(gT_map))) c P).

Notation "⚡={ M }=> P" := (nextgen_omega M P)
                            (at level 99, M at level 50, P at level 200, format "⚡={ M }=>  P") : bi_scope.

Local Existing Instances noTransInG_A_inG noTransInG_B_inG noTransInG_inG.

Definition bnextgen_bounded_ind {Σ : gFunctors} {A : cmra} {pick : pick_transform_rel A}
  (Ω : gTransformations Σ) `{!noTwoTransInG Σ Ω (gmap_viewR positive (optionO (leibnizO C))) A} (c : C) (P : iProp Σ) : iProp Σ :=
  ⚡◻{ (CR,λ c, build_trans (gT_map (transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω))) ↑ c} P.

Notation "⚡◻{ Ω ↑ c } P" := (bnextgen_bounded_ind Ω c P)
                               (at level 99, Ω at level 50, c at level 20, P at level 200, format "⚡◻{ Ω  ↑  c }  P") : bi_scope.


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

  Lemma bnextgen_bounded_ind_if_always P c b :
    (□?b ⚡◻{ Ω ↑ c } P) ⊣⊢ (⚡◻{ Ω ↑ c } □?b P).
  Proof.
    destruct b;simpl.
    - apply bnextgen_ind_always.
    - auto. 
  Qed.

  Lemma bnextgen_bounded_ind_GenIndependent_intro P c :
    GenIndependent2Ω Ω c P ->
    P ⊢ ⚡◻{ Ω ↑ c } P.
  Proof.
    rewrite /GenIndependent.
    iIntros (HP) "HP".
    iApply bnextgen_ind_intro;auto.
  Qed.

  Lemma gen_ind_insert2_intro P c c' :
    GenIndependent2Ω Ω c P ->
    rc CR c c' ->
    P ⊢ ⚡={transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω}=> P.
  Proof.
    rewrite /GenIndependent.
    intros Hind Hcr.
    apply Hind in Hcr;auto.
  Qed.
  
End bnextgen_bounded_ind_rules.
