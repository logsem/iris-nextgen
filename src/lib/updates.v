From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

(** * Restricted frame preserving updates *)
(* This quantifies over [option A] for the frame.  That is necessary
   to make the following hold: x ~~> P → Some c ~~> Some P

   Also quantifies over a cmra and cmramorphism and restricts the
   considered frames to be those that are not altered by that
   morphism *)
(* Definition cmra_updateP {A : cmra} (t : A → A) `{!CmraMorphism t} (x : A) (P : A → Prop) := ∀ n mz, *)
(*   ✓{n} (x ⋅? mz) -> from_option (λ mz, t mz ≡ mz) True mz → ∃ y, P y ∧ t y ≡ y /\ ✓{n} (y ⋅? mz). *)
(* Global Instance: Params (@cmra_updateP) 1 := {}. *)
(* Global Instance: Params (@cmra_updateP) 3 := {}. *)
(* Infix "~~>:{  t  }" := (cmra_updateP t) (at level 70). *)

Definition cmra_updateP {A : cmra} (t : A → A) `{!CmraMorphism t} (x : A) (P : A → Prop) := ∀ n mz,
  ✓{n} (t x ⋅? mz) -> ∃ y, P (t y) ∧ ✓{n} (t y ⋅? mz).
Global Instance: Params (@cmra_updateP) 1 := {}.
Global Instance: Params (@cmra_updateP) 3 := {}.
Infix "~~>:{  t  }" := (cmra_updateP t) (at level 70).

(* Definition cmra_update {A : cmra} (t : A → A) `{!CmraMorphism t} (x y : A) := ∀ n mz, *)
(*   ✓{n} (x ⋅? mz) -> from_option (λ mz, t mz ≡ mz) True mz → t y ≡ y /\ ✓{n} (y ⋅? mz). *)
(* Infix "~~>{  t  }" := (cmra_update t) (at level 70). *)
(* Global Instance: Params (@cmra_update) 1 := {}. *)
(* Global Instance: Params (@cmra_update) 3 := {}. *)

Definition cmra_update {A : cmra} (t : A → A) `{!CmraMorphism t} (x y : A) := ∀ n mz,
  ✓{n} (t x ⋅? mz) -> ✓{n} (t y ⋅? mz).
Infix "~~>{  t  }" := (cmra_update t) (at level 70).
Global Instance: Params (@cmra_update) 1 := {}.
Global Instance: Params (@cmra_update) 3 := {}.


Section updates.
Context {A : cmra} (t : A -> A) `{morph: !CmraMorphism t}.
Implicit Types x y : A.

Global Instance cmra_updateP_proper :
  Proper ((≡) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP A t morph).
Proof.
  rewrite /pointwise_relation /cmra_updateP=> x x' Hx P P' HP;
    split=> ? n mz; setoid_subst; naive_solver.
Qed.
Global Instance cmra_update_proper :
  Proper ((≡) ==> (≡) ==> iff) (@cmra_update A t morph).
Proof.
  rewrite /cmra_update=> x x' Hx y y' Hy; split=> BB n mz E; setoid_subst;auto.
Qed.

Lemma cmra_update_updateP x y : x ~~>{t} y ↔ x ~~>:{t} (t y =.).
Proof. split=> Hup n z ?; eauto; destruct (Hup n z) as (?&<-&?);auto. Qed.
Lemma cmra_update_updateP' x y : x ~~>{t} y ↔ x ~~>:{t} (t y ≡.).
Proof. split=> Hup n z ?; eauto; destruct (Hup n z) as (?&<-&?);auto. Qed.
Lemma cmra_updateP_id (P : A → Prop) x : P (t x) -> x ~~>:{t} P.
Proof. intros ? n mz ?; eauto. Qed.
Lemma cmra_updateP_compose (P Q : A → Prop) x :
  x ~~>:{t} P → (∀ y, P (t y) -> y ~~>:{t} Q) → x ~~>:{t} Q.
Proof. intros Hx Hy n mz ?. destruct (Hx n mz) as (y&?&?); naive_solver. Qed.
Lemma cmra_updateP_compose_l (Q : A → Prop) x y : x ~~>{t} y → y ~~>:{t} Q → x ~~>:{t} Q.
Proof.
  rewrite cmra_update_updateP.
  intros Ht Hcond ???. edestruct Ht as [? [Heq B]];eauto.
  rewrite -Heq in B. apply Hcond in B;eauto.
Qed.
Lemma cmra_updateP_weaken (P Q : A → Prop) x :
  x ~~>:{t} P → (∀ y, P y → Q y) → x ~~>:{t} Q.
Proof. eauto using cmra_updateP_compose, cmra_updateP_id. Qed.

Lemma cmra_update_exclusive `{!Exclusive (t x)} y:
  ✓ y -> x ~~>{t} y.
Proof. move=>??[z|]=>[/exclusiveN_l[]|_]. simpl. apply cmra_morphism_validN=>//.
       by apply cmra_valid_validN. Qed.

(** Updates form a preorder. *)
(** We set this rewrite relation's cost above the stdlib's
  ([impl], [iff], [eq], ...) and [≡] but below [⊑].
  [eq] (at 100) < [≡] (at 150) < [cmra_update] (at 170) < [⊑] (at 200) *)
Global Instance cmra_update_rewrite_relation :
  RewriteRelation (@cmra_update A t morph) | 170 := {}.
Global Instance cmra_update_preorder : PreOrder (@cmra_update A t morph).
Proof.
  split.
  - intros x. apply cmra_update_updateP, cmra_updateP_id;auto.
  - intros x y z. rewrite !cmra_update_updateP.
    intros Hx Hy. intros n mz Hv. apply Hx in Hv as [y' [Heq1 Hy']].
    rewrite -Heq1 in Hy'. apply Hy in Hy' as [? [? ?]];eauto.
Qed.
Global Instance cmra_update_proper_update :
  Proper (flip (@cmra_update A t morph) ==> (@cmra_update A t morph) ==> impl) (@cmra_update A t morph).
Proof.
  intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
Qed.
Global Instance cmra_update_flip_proper_update :
  Proper ((@cmra_update A t morph) ==> flip (@cmra_update A t morph) ==> flip impl) (@cmra_update A t morph).
Proof.
  intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
Qed.

Lemma cmra_updateP_op (P1 P2 Q : A → Prop) x1 x2 :
  x1 ~~>:{t} P1 → x2 ~~>:{t} P2 → (∀ y1 y2, P1 (t y1) → P2 (t y2) → Q (t (y1 ⋅ y2))) →
  x1 ⋅ x2 ~~>:{t} Q.
Proof.
  intros Hx1 Hx2 Hy n mz ?.
  destruct (Hx1 n (Some (t x2 ⋅? mz))) as (y1&?&?).
  { rewrite /= -cmra_op_opM_assoc. rewrite -cmra_morphism_op//. }
  destruct (Hx2 n (Some (t y1 ⋅? mz))) as (y2&?&?).
  { rewrite /= -cmra_op_opM_assoc (comm _ (t x2)) cmra_op_opM_assoc. auto. }
  exists (y1 ⋅ y2); split; try rewrite cmra_morphism_op; last rewrite (comm _ (t y1)) cmra_op_opM_assoc; auto.
Qed.
Lemma cmra_updateP_op' (P1 P2 : A → Prop) x1 x2 :
  x1 ~~>:{t} P1 → x2 ~~>:{t} P2 →
  x1 ⋅ x2 ~~>:{t} λ y, ∃ y1 y2, y ≡ t (y1) ⋅ t (y2) ∧ P1 (t y1) ∧ P2 (t y2).
Proof. eauto 10 using cmra_updateP_op, cmra_morphism_op. Qed.
Lemma cmra_update_op x1 x2 y1 y2 : x1 ~~>{t} y1 → x2 ~~>{t} y2 → x1 ⋅ x2 ~~>{t} y1 ⋅ y2.
Proof.
  rewrite !cmra_update_updateP'.
  intros HP1 HP2 n mz Hx12.
  rewrite cmra_morphism_op in Hx12.
  destruct (HP1 n (Some (t x2 ⋅? mz))) as (y1'&?&?);[rewrite /=;auto|].
  { rewrite /= -cmra_op_opM_assoc. auto. }
  destruct (HP2 n (Some (t y1' ⋅? mz))) as (y2'&?&?).
  { rewrite /= -cmra_op_opM_assoc (comm _ (t x2)) cmra_op_opM_assoc. auto. }
  simpl in *. exists (y1' ⋅ y2').
  rewrite !cmra_morphism_op H H1. repeat split;auto; last rewrite (comm _ (t y1')) cmra_op_opM_assoc; auto.
Qed.

Global Instance cmra_update_op_proper :
  Proper ((@cmra_update A t morph) ==> (@cmra_update A t morph) ==> (@cmra_update A t morph)) (op (A:=A)).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_op. Qed.
Global Instance cmra_update_op_flip_proper :
  Proper (flip (@cmra_update A t morph) ==> flip (@cmra_update A t morph) ==> flip (@cmra_update A t morph)) (op (A:=A)).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_op. Qed.

Lemma cmra_update_op_l x y : x ⋅ y ~~>{t} x.
Proof. intros n mz. rewrite cmra_morphism_op. rewrite comm cmra_op_opM_assoc. apply cmra_validN_op_r. Qed.
Lemma cmra_update_op_r x y : x ⋅ y ~~>{t} y.
Proof. rewrite comm. apply cmra_update_op_l. Qed.

Lemma cmra_update_included x y : x ≼ y → y ~~>{t} x.
Proof. intros [z ->]. apply cmra_update_op_l. Qed.

Lemma cmra_update_valid0 x y : (✓{0} t x → x ~~>{t} y) → x ~~>{t} y.
Proof.
  intros H n mz Hmz. apply H, Hmz.
  apply (cmra_validN_le n); last lia.
  destruct mz.
  - eapply cmra_validN_op_l, Hmz.
  - apply Hmz.
Qed.

(** ** Frame preserving updates for total CMRAs *)
Section total_updates.
  Local Set Default Proof Using "Type*".
  Context `{!CmraTotal A}.

  Lemma cmra_total_updateP x (P : A → Prop) :
    x ~~>:{t} P ↔ ∀ n z, ✓{n} (t x ⋅ z) → ∃ y, P (t y) ∧ ✓{n} (t y ⋅ z).
  Proof.
    split=> Hup; [intros n z ?; apply (Hup n (Some z))|];auto.
    intros n [z|] ?; simpl; [by apply Hup|].
    destruct (Hup n (core (t x))) as (y&?&?).
    - destruct morph. specialize (cmra_morphism_pcore x).
      rewrite !cmra_pcore_core /= in cmra_morphism_pcore.
      inversion cmra_morphism_pcore;subst. rewrite -H2.
      rewrite -cmra_morphism_op cmra_core_r //.
    - eauto using cmra_validN_op_l.
  Qed.
  Lemma cmra_total_update x y : x ~~>{t} y ↔ ∀ n z, ✓{n} (t x ⋅ z) → ✓{n} (t y ⋅ z).
  Proof. rewrite cmra_update_updateP cmra_total_updateP. split;intros;eauto.
         edestruct H as [? [-> H']];eauto. Qed.

  Context `{!CmraDiscrete A}.

  Lemma cmra_discrete_updateP (x : A) (P : A → Prop) :
    x ~~>:{t} P ↔ ∀ z, ✓ (t x ⋅ z) → ∃ y, P (t y) ∧ ✓ (t y ⋅ z).
  Proof.
    rewrite cmra_total_updateP; setoid_rewrite <-cmra_discrete_valid_iff.
    naive_solver eauto using O.
  Qed.
  Lemma cmra_discrete_update (x y : A) :
    x ~~>{t} y ↔ ∀ z, ✓ (t x ⋅ z) → ✓ (t y ⋅ z).
  Proof.
    rewrite cmra_total_update; setoid_rewrite <-cmra_discrete_valid_iff.
    naive_solver eauto using O.
  Qed.
End total_updates.
End updates.

(** * Product *)
Section prod.
  Context {A B : cmra} (f : B -> B) (t : A -> A) `{morphf: !CmraMorphism f} `{morpht: !CmraMorphism t}.
  Implicit Types x : A * B.

  Lemma prod_updateP P1 P2 (Q : A * B → Prop) x :
    x.1 ~~>:{t} P1 → x.2 ~~>:{f} P2 → (∀ a b, P1 (t a) → P2 (f b) → Q (t a,f b)) → x ~~>:{λ x, (t x.1,f x.2)} Q.
  Proof.
    intros Hx1 Hx2 HP n mz [??]; simpl in *.
    destruct (Hx1 n (fst <$> mz)) as (a&?&?); first by destruct mz.
    destruct (Hx2 n (snd <$> mz)) as (b&?&?); first by destruct mz.
    exists (a,b); repeat split; destruct mz; auto.
  Qed.
  Lemma prod_updateP' P1 P2 x :
    x.1 ~~>:{t} P1 → x.2 ~~>:{f} P2 → x ~~>:{λ x, (t x.1,f x.2)} λ y, P1 y.1 ∧ P2 y.2.
  Proof. eauto using prod_updateP. Qed.
  Lemma prod_update x y : x.1 ~~>{t} y.1 → x.2 ~~>{f} y.2 → x ~~>{λ x, (t x.1, f x.2)} y.
  Proof.
    rewrite !cmra_update_updateP.
    destruct x, y; simpl.
    intros. eapply prod_updateP;eauto.
    intros a b -> -> =>//.
  Qed.
End prod.

(** * Option *)
Section option.
  Context {A : cmra} (t : A -> A) `{morph: !CmraMorphism t}.
  Implicit Types x y : A.

  Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x :
    x ~~>:{t} P → (∀ y, P (t y) → Q (Some (t y))) → Some x ~~>:{λ (x : option A), x ≫= (λ x, Some (t x))} Q (* (λ x, Q (Some x)) *).
  Proof.
    intros Hx Hy. intros n mz Hn. destruct mz. 
    { simpl in *. rewrite Some_op_opM in Hn. apply Hx in Hn as [? [? ?]].
      eexists (Some x0). rewrite Some_op_opM /=. naive_solver. }
    simpl in *. rewrite Some_validN in Hn. edestruct (Hx n None) as [? [? ?]];auto.
    eexists (Some _). simpl. eauto.
  Qed.
  Lemma option_update x y : x ~~>{t} y → Some x ~~>{λ (x : option A), x ≫= (λ x, Some (t x))} Some y.
  Proof. rewrite !cmra_update_updateP. intros. eapply option_updateP;eauto.
         intros. simpl. f_equiv;auto. Qed.
End option.
