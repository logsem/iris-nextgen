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


(* ∃ x' x1' x2', x' ≡{k}≡ x1' ⋅ x2' /\ x1' ≡{k}≡ t x1' *)
(*                                             /\ (∃ x2, x ≡{k}≡ x2 ⋅ x2' /\ (∀ x3 x2'' yf', x2 ≡{k}≡ t x3 -> x2' ≡{k}≡ t x2'' -> yf ≡{k}≡ t yf' -> *)
(*                                                                                         ✓{k} (x3 ⋅ x2'' ⋅ yf') -> ✓{k} (x1' ⋅ x2'' ⋅ yf'))) *)
(*                                             /\ ✓{k} (x' ⋅ yf) *)
(*               /\ Q k x' *)


Definition upd_img_rel {A : cmra} (t : A → A) `{!CmraMorphism t} (x1 y1 y2 : A) (mz : option A) (k : nat) :=
  (∀ x1' y2' mz', x1 ≡{k}≡ t x1' -> y2 ≡{k}≡ t y2' -> (from_option (λ a, mz' ≡{k}≡ Some (t a)) (mz' ≡{k}≡ None) mz) ->
                  ✓{k} (x1' ⋅ y2' ⋅? mz') -> ✓{k} (y1 ⋅ y2' ⋅? mz')).
Definition upd_rel {A : cmra} (t : A → A) `{!CmraMorphism t} (x : A) (y : A) (k : nat) (mz : option A) :=
  ∃ (y1 y2 x1: A), (y ≡{k}≡ y1 ⋅ y2 /\ t y1 ≡{k}≡ y1 /\ x ≡{k}≡ x1 ⋅ y2) /\ upd_img_rel t x1 y1 y2 mz k.
  

Definition cmra_updateP {A : cmra} (t : A → A) `{!CmraMorphism t} (x : A) (P : A → Prop) := ∀ n (mz : option A),
    ✓{n} (x ⋅? mz) -> ∃ y, P (y) /\ ✓{n} (y ⋅? mz) /\ upd_rel t x y n mz.
Global Instance: Params (@cmra_updateP) 1 := {}.
Global Instance: Params (@cmra_updateP) 3 := {}.
Infix "~~>:{  t  }" := (cmra_updateP t) (at level 70).

(* Definition cmra_update {A : cmra} (t : A → A) `{!CmraMorphism t} (x y : A) := ∀ n mz, *)
(*   ✓{n} (x ⋅? mz) -> from_option (λ mz, t mz ≡ mz) True mz → t y ≡ y /\ ✓{n} (y ⋅? mz). *)
(* Infix "~~>{  t  }" := (cmra_update t) (at level 70). *)
(* Global Instance: Params (@cmra_update) 1 := {}. *)
(* Global Instance: Params (@cmra_update) 3 := {}. *)

Definition cmra_update {A : cmra} (t : A → A) `{!CmraMorphism t} (x y : A) := ∀ n mz,
  ✓{n} (x ⋅? mz) -> ✓{n} (y ⋅? mz) /\ upd_rel t x y n mz.
Infix "~~>{  t  }" := (cmra_update t) (at level 70).
Global Instance: Params (@cmra_update) 1 := {}.
Global Instance: Params (@cmra_update) 3 := {}.



(* Lemma equiv_Some_l {A : cmra} (c : A) (mz : option A) : *)
(*   Some c ≡ mz -> ∃ (c' : A), mz = Some c' /\ c' ≡ c. *)
(* Proof. *)
(*   intros Hc. *)
(*   inversion Hc;subst;eauto. *)
(* Qed. *)

Class GenTransContractive {A : cmra} (f : A -> A) := {
    gen_trans_contr n a : (f a ≼{n} a)
}.

Section updates.
Context {A : ucmra} (t : A -> A) `{morph: !CmraMorphism t} `{!GenTransContractive t}.
Implicit Types x y : A.

Global Instance upd_img_rel_proper :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (=) ==> iff) (@upd_img_rel A t morph).
Proof.
  intros ??? y1 y2 Hy ??? mz mz' Hmz ???;subst.
  rewrite /upd_img_rel. split=> Hyp???????;[rewrite -Hy|rewrite Hy]; eapply Hyp;eauto;
  destruct mz;simpl;inversion Hmz;subst;simpl in *;setoid_subst;auto.
Qed.
  
Global Instance upd_rel_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (≡) ==> iff) (@upd_rel A t morph).
Proof.
  intros x x' Hx y y' Hy n1 n2 Heq mz mz' Hmz;subst.
  split=> [[x1[x2[x3[HH Hyp]]]]|[x1[x2[x3[HH Hyp]]]]]; exists x1,x2,x3;split;[rewrite -Hx -Hy//| |rewrite Hx Hy//|];
  (intros ???????; eapply Hyp;eauto;
   destruct mz';simpl;[apply Some_equiv_eq in Hmz as [c' [-> Hc']]|inversion Hmz;subst];simpl in *;auto);[rewrite Hc'//|rewrite -Hc'//].
Qed.

Global Instance cmra_updateP_proper :
  Proper ((≡) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP A t morph).
Proof.
  rewrite /pointwise_relation /cmra_updateP=> x x' Hx P P' HP;
    split=> Hyp n mz;[erewrite <- Hx|erewrite Hx];intros HH;
    apply Hyp in HH as [y [??]];exists y; setoid_subst; naive_solver.
Qed.
Global Instance cmra_update_proper :
  Proper ((≡) ==> (≡) ==> iff) (@cmra_update A t morph).
Proof.
  rewrite /cmra_update=> x x' Hx y y' Hy; split=> BB n mz E; setoid_subst;auto.
Qed.
  
Lemma cmra_update_updateP x y : x ~~>{t} y ↔ x ~~>:{t} (y =.).
Proof. split=> Hup n z HH; eauto; destruct (Hup n z) as (?&<-&?&?);auto. Qed.
Lemma cmra_update_updateP' x y : x ~~>{t} y ↔ x ~~>:{t} (y ≡.).
Proof. split=> Hup n z ?; eauto; destruct (Hup n z) as (?&<-&?);auto. Qed.
(* Lemma cmra_updateP_id (P : A → Prop) x : P (x) -> x ~~>:{t} P. *)
(* Proof. intros Heq n mz ?; eauto. Qed. *)
(* Lemma cmra_updateP_compose (P Q : A → Prop) x : *)
(*   x ~~>:{t} P → (∀ y, P y -> t y ≡ y -> y ~~>:{t} Q) → x ~~>:{t} Q. *)
(* Proof. intros Hx Hy n mz ?. destruct (Hx n mz) as (y&HP&Heq&?); naive_solver. Qed. *)
(* Lemma cmra_updateP_compose_l (Q : A → Prop) x y : x ~~>{t} y → y ~~>:{t} Q → x ~~>:{t} Q. *)
(* Proof. *)
(*   rewrite cmra_update_updateP. *)
(*   intros Ht Hcond ???. edestruct Ht as [? [Heq [B Hequiv]]];eauto. *)
(*   rewrite -Heq in B. subst. edestruct Hcond as (?&?&?&?);[rewrite Hequiv;eauto|];eauto. Qed. *)
(* Lemma cmra_updateP_weaken (P Q : A → Prop) x : *)
(*   x ~~>:{t} P → (∀ y, P y → Q y) → x ~~>:{t} Q. *)
(* Proof. eauto using cmra_updateP_compose, cmra_updateP_id. Qed. *)

(* Lemma cmra_update_exclusive `{!Exclusive x} y: *)
(*   ✓ y -> t y ≡ y -> x ~~>{t} y. *)
(* Proof. move=>???[z|] =>[[/exclusiveN_l[] ?]|[? ?]];simpl. split;auto. *)
(*        by apply cmra_valid_validN. Qed. *)

(* (** Updates form a preorder. *) *)
(* (** We set this rewrite relation's cost above the stdlib's *)
(*   ([impl], [iff], [eq], ...) and [≡] but below [⊑]. *)
(*   [eq] (at 100) < [≡] (at 150) < [cmra_update] (at 170) < [⊑] (at 200) *) *)
(* Global Instance cmra_update_rewrite_relation : *)
(*   RewriteRelation (@cmra_update A t morph) | 170 := {}. *)
(* Global Instance cmra_update_preorder : PreOrder (@cmra_update A t morph). *)
(* Proof. *)
(*   split. *)
(*   - intros x. apply cmra_update_updateP, cmra_updateP_id;auto. *)
(*   - intros x y z. rewrite !cmra_update_updateP. *)
(*     intros Hx Hy. intros n mz Hv. apply Hx in Hv as [y' [Heq1 Hy']]. *)
(*     rewrite -Heq1 in Hy'. edestruct Hy;eauto. *)
(* Qed. *)
(* Global Instance cmra_update_proper_update : *)
(*   Proper (flip (@cmra_update A t morph) ==> (@cmra_update A t morph) ==> impl) (@cmra_update A t morph). *)
(* Proof. *)
(*   intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy]. *)
(* Qed. *)
(* Global Instance cmra_update_flip_proper_update : *)
(*   Proper ((@cmra_update A t morph) ==> flip (@cmra_update A t morph) ==> flip impl) (@cmra_update A t morph). *)
(* Proof. *)
(*   intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy]. *)
(* Qed. *)

(* Lemma cmra_morphism_option_op : *)
(*   forall (x : A) (y : option A), t (x ⋅? y) ≡ t x ⋅? (y ≫= t). *)
(* Proof using morph. *)
(*   intros x y. destruct y;simpl;auto. *)
(*   by apply cmra_morphism_op. *)
(* Qed. *)

(* Lemma cmra_updateP_op (P1 P2 Q : A → Prop) x1 x2 : *)
(*   x1 ~~>:{t} P1 → x2 ~~>:{t} P2 → *)
(*   (∀ y1 y2, P1 (y1) → P2 (y2) → Q (y1 ⋅ y2)) → *)
(*   (∀ x x1 x2, t x ≡ x -> x ≡ x1 ⋅ x2 -> t x1 ≡ x1) -> *)
(*   x1 ⋅ x2 ~~>:{t} Q. *)
(* Proof. *)
(*   intros Hx1 Hx2 Hy Hx n mz [Hv Heq]. *)
(*   destruct (Hx1 n (Some (x2 ⋅? mz))) as (y1&?&?&Heq1). *)
(*   { simpl in *. rewrite -cmra_op_opM_assoc//. apply (Hx (x1 ⋅ x2) x1 x2) in Heq =>//. } *)
(*   destruct (Hx2 n (Some (t y1 ⋅? mz))) as (y2&?&Hv2&Heq2). *)
(*   { rewrite /= -cmra_op_opM_assoc (comm _ x2) cmra_op_opM_assoc. *)
(*     apply (Hx (x1 ⋅ x2) x2 x1) in Heq;[|rewrite comm//]. rewrite Heq1. auto. } *)
(*   exists (y1 ⋅ y2). rewrite Heq1 in Hv2. *)
(*   split; try rewrite cmra_morphism_op; last rewrite {1}(comm _ (y1)) cmra_op_opM_assoc; auto. *)
(*   rewrite Heq1 Heq2 //. *)
(* Qed. *)
(* Lemma cmra_updateP_op' (P1 P2 : A → Prop) x1 x2 : *)
(*   x1 ~~>:{t} P1 → x2 ~~>:{t} P2 → *)
(*   (∀ x x1 x2, t x ≡ x -> x ≡ x1 ⋅ x2 -> t x1 ≡ x1) -> *)
(*   x1 ⋅ x2 ~~>:{t} λ y, ∃ y1 y2, y ≡ y1 ⋅ y2 /\ P1 y1 ∧ P2 y2. *)
(* Proof. eauto 10 using cmra_updateP_op. Qed. *)
(* Lemma cmra_update_op x1 x2 y1 y2 : *)
(*   (∀ x x1 x2, t x ≡ x -> x ≡ x1 ⋅ x2 -> t x1 ≡ x1) -> *)
(*   x1 ~~>{t} y1 → x2 ~~>{t} y2 → x1 ⋅ x2 ~~>{t} y1 ⋅ y2. *)
(* Proof. *)
(*   rewrite !cmra_update_updateP'. *)
(*   intros Hop HP1 HP2 n mz [Hv Hx12]. *)
(*   destruct (HP1 n (Some (x2 ⋅? mz))) as (y1'&?&?&Heq1);[rewrite /=;auto|]. *)
(*   { rewrite /= -cmra_op_opM_assoc. apply (Hop (x1 ⋅ x2) x1 x2) in Hx12;auto. } *)
(*   destruct (HP2 n (Some (y1' ⋅? mz))) as (y2'&?&?&Heq2). *)
(*   { rewrite /= -cmra_op_opM_assoc (comm _ (x2)) cmra_op_opM_assoc. *)
(*     apply (Hop (x1 ⋅ x2) x2 x1) in Hx12;auto. by rewrite comm. } *)
(*   simpl in *. exists (y1' ⋅ y2'). *)
(*   rewrite !cmra_morphism_op H H1. *)
(*   repeat split;auto; first rewrite (comm _ (y1')) cmra_op_opM_assoc; auto. *)
(*   rewrite Heq1 Heq2 //. *)
(* Qed. *)

(* Global Instance cmra_update_op_proper : *)
(*   Proper ((@cmra_update A t morph) ==> (@cmra_update A t morph) ==> (@cmra_update A t morph)) (op (A:=A)). *)
(* Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_op. Qed. *)
(* Global Instance cmra_update_op_flip_proper : *)
(*   Proper (flip (@cmra_update A t morph) ==> flip (@cmra_update A t morph) ==> flip (@cmra_update A t morph)) (op (A:=A)). *)
(* Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_op. Qed. *)

(* Lemma cmra_update_op_l x y : x ⋅ y ~~>{t} x. *)
(* Proof. intros n mz. rewrite cmra_morphism_op. rewrite comm cmra_op_opM_assoc. apply cmra_validN_op_r. Qed. *)
(* Lemma cmra_update_op_r x y : x ⋅ y ~~>{t} y. *)
(* Proof. rewrite comm. apply cmra_update_op_l. Qed. *)

(* Lemma cmra_update_included x y : x ≼ y → y ~~>{t} x. *)
(* Proof. intros [z ->]. apply cmra_update_op_l. Qed. *)

(* Lemma cmra_update_valid0 x y : (✓{0} x → x ~~>{t} y) → x ~~>{t} y. *)
(* Proof. *)
(*   intros H n mz Hmz. apply H, Hmz. *)
(*   apply (cmra_validN_le n); last lia. *)
(*   destruct mz. *)
(*   - eapply cmra_validN_op_l, Hmz. *)
(*   - apply Hmz. *)
(* Qed. *)

(* (** ** Frame preserving updates for total CMRAs *) *)
(* Section total_updates. *)
(*   Local Set Default Proof Using "Type*". *)
(*   Context `{!CmraTotal A}. *)

(*   Lemma cmra_total_updateP x (P : A → Prop) : *)
(*     x ~~>:{t} P ↔ ∀ n z, ✓{n} (x ⋅ z) /\ t x ≡ x → ∃ y, P (y) ∧ ✓{n} (y ⋅ z) /\ t y ≡ y. *)
(*   Proof. *)
(*     split=> Hup; [intros n z ?; apply (Hup n (Some z))|];auto. *)
(*     intros n [z|] [? Heq]; simpl; [by apply Hup|]. *)
(*     destruct (Hup n (core (t x))) as (y&?&?&Heq2). *)
(*     - destruct morph. specialize (cmra_morphism_pcore x). *)
(*       rewrite !cmra_pcore_core /= in cmra_morphism_pcore. *)
(*       inversion cmra_morphism_pcore;subst. rewrite -H2. *)
(*       rewrite H2 Heq cmra_core_r //. *)
(*     - eauto using cmra_validN_op_l. *)
(*   Qed. *)
(*   Lemma cmra_total_update x y : x ~~>{t} y ↔ ∀ n z, ✓{n} (x ⋅ z) /\ t x ≡ x → ✓{n} (y ⋅ z) /\ t y ≡ y. *)
(*   Proof. rewrite cmra_update_updateP cmra_total_updateP. split;intros;eauto. *)
(*          edestruct H as [? [-> H']];eauto. Qed. *)

(*   Context `{!CmraDiscrete A}. *)

(*   Lemma cmra_discrete_updateP (x : A) (P : A → Prop) : *)
(*     x ~~>:{t} P ↔ ∀ z, ✓ (x ⋅ z) /\ t x ≡ x → ∃ y, P (y) ∧ ✓ (y ⋅ z) /\ t y ≡ y. *)
(*   Proof. *)
(*     rewrite cmra_total_updateP; setoid_rewrite <-cmra_discrete_valid_iff. *)
(*     naive_solver eauto using O. *)
(*   Qed. *)
(*   Lemma cmra_discrete_update (x y : A) : *)
(*     x ~~>{t} y ↔ ∀ z, ✓ (x ⋅ z) /\ t x ≡ x → ✓ (y ⋅ z) /\ t y ≡ y. *)
(*   Proof. *)
(*     rewrite cmra_total_update; setoid_rewrite <-cmra_discrete_valid_iff. *)
(*     naive_solver eauto using O. *)
(*   Qed. *)
(* End total_updates. *)
End updates.

(* (** * Product *) *)
(* Section prod. *)
(*   Context {A B : cmra} (f : B -> B) (t : A -> A) `{morphf: !CmraMorphism f} `{morpht: !CmraMorphism t}. *)
(*   Implicit Types x : A * B. *)

(*   Lemma prod_updateP P1 P2 (Q : A * B → Prop) x : *)
(*     x.1 ~~>:{t} P1 → x.2 ~~>:{f} P2 → (∀ a b, P1 (a) → P2 (b) → Q (a,b)) → x ~~>:{λ x, (t x.1,f x.2)} Q. *)
(*   Proof. *)
(*     intros Hx1 Hx2 HP n mz [[??][??]]; simpl in *. *)
(*     destruct (Hx1 n (fst <$> mz)) as (a&?&?&?); first by destruct mz. *)
(*     destruct (Hx2 n (snd <$> mz)) as (b&?&?&?); first by destruct mz. *)
(*     exists (a,b); repeat split; destruct mz; auto. *)
(*   Qed. *)
(*   Lemma prod_updateP' P1 P2 x : *)
(*     x.1 ~~>:{t} P1 → x.2 ~~>:{f} P2 → x ~~>:{λ x, (t x.1,f x.2)} λ y, P1 y.1 ∧ P2 y.2. *)
(*   Proof. eauto using prod_updateP. Qed. *)
(*   Lemma prod_update x y : x.1 ~~>{t} y.1 → x.2 ~~>{f} y.2 → x ~~>{λ x, (t x.1, f x.2)} y. *)
(*   Proof. *)
(*     rewrite !cmra_update_updateP. *)
(*     destruct x, y; simpl. *)
(*     intros. eapply prod_updateP;eauto. *)
(*     intros a b -> -> =>//. *)
(*   Qed. *)
(* End prod. *)

(* Local Infix "≫=" := (λ mz t, (mz ≫= (λ x, Some (t x)))). *)

(* (** * Option *) *)
(* Section option. *)
(*   Context {A : cmra} (t : A -> A) `{morph: !CmraMorphism t}. *)
(*   Implicit Types x y : A. *)

(*   Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x : *)
(*     x ~~>:{t} P → (∀ y, P (y) → Q (Some (y))) → Some x ~~>:{λ (x : option A), x ≫= t} Q. *)
(*   Proof. *)
(*     intros Hx Hy. intros n mz Hn. destruct mz. *)
(*     { simpl in *. rewrite Some_op_opM Some_validN in Hn. destruct Hn as [Hv Hn]. *)
(*       inversion Hn;subst. edestruct Hx as [? [? [? ?]]];eauto. *)
(*       eexists (Some x0). rewrite Some_op_opM /=. repeat split;auto. f_equiv. auto. } *)
(*     simpl in *. rewrite Some_validN in Hn. destruct Hn as [Hv Hn]. *)
(*     inversion Hn;subst. *)
(*     edestruct (Hx n None) as [? [? [? ?]]];auto. *)
(*     eexists (Some _). simpl. repeat split; eauto. f_equiv. auto. *)
(*   Qed. *)
(*   Lemma option_update x y : x ~~>{t} y → Some x ~~>{λ (x : option A), x ≫= t} Some y. *)
(*   Proof. rewrite !cmra_update_updateP. intros. eapply option_updateP;eauto. *)
(*          intros. simpl. f_equiv;auto. Qed. *)
(* End option. *)
