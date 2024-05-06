From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From nextgen Require Import cmra_morphism_extra.
From nextgen Require Export nextgen_pointwise gmap_view_transformation nextgen_basic utils.
Import uPred.

(** * Class to pick transformations based on transitive relation over chosen type *)


(* Reflexite closure *)
Inductive rc {A : Type} (R : relation A) : relation A :=
| rc_once x y : R x y → rc R x y
| rc_l x : rc R x x.

Global Instance rc_refl {A : Type} (R : relation A) : Reflexive (rc R).
Proof. intros ?. apply rc_l. Qed.

Global Instance rc_dec {A : Type} (R : relation A) `{!EqDecision A} `{!∀ c1 c2, Decision (R c1 c2)} (c1 c2 : A) : Decision (rc R c1 c2).
Proof.
  destruct (decide (c1 = c2));subst.
  - left. apply rc_l.
  - destruct (decide (R c1 c2));[left|right].
    + constructor. auto.
    + intros Hcontr;inversion Hcontr;done.
Qed.

Global Instance rc_trans {A : Type} (R : relation A) `{!Transitive R} : Transitive (rc R).
Proof.
  intros c1 c2 c3 Hr1 Hr2.
  inversion Hr1; inversion Hr2;subst;auto.
  constructor. etrans;eauto.
Qed.

Class ComposeSubsume {A C} (eqR: relation A) (R: relation C) (f : C -> A -> A) : Prop :=
  compose_subsume c1 c2 x : R c1 c2 -> eqR (f c1 (f c2 x)) (f c1 x).

Class pick_transform_rel (A : cmra) : Type := TransRel {
  C : Type;
  CR : relation C;
  C_bot : C;                                
  C_total : Trichotomy CR;
  C_pre :> Transitive CR;
  C_pick : C -> (A -> A);
  C_pick_cmramorphism :> ∀ (c : C), CmraMorphism (C_pick c);
  C_pick_idemp :> ∀ (c : C), Idemp equiv (C_pick c);
  C_indep :> ∀ (c1 c2 : C), Indep equiv (C_pick c1) (C_pick c2);
  C_comp :> ComposeSubsume equiv CR C_pick;
  C_dec :> ∀ (c1 c2 : C), Decision (CR c1 c2);
  C_eq_dec :> EqDecision C; }.

Global Existing Instance C_pick_cmramorphism.
(* #[global] Instance cmra_morphism_pick `{Hpre : pick_transform_rel A} : ∀ c', CmraMorphism (C_pick c') := *)
(*   Hpre.(C_pick_cmramorphism). *)

Definition inv_pick_cut `{pick_transform_rel A} (c : C) (i : positive) (v : optionO (leibnizO C)) :=
 Some (v ≫= (λ c', if decide (rc CR c' c) then Some c' else None)).
Definition inv_pick_transform `{pick_transform_rel A} (c : C) := (map_entry_lift_gmap_view (inv_pick_cut c)).

#[global] Instance inv_pick_mapTrans `{pick_transform_rel A} (c : C) : MapTrans (inv_pick_cut c).
Proof.
  split.
  - intros l v1 Hcontr. done.
  - intros l v v' Hl.
    rewrite /inv_pick_cut /=.
    rewrite /inv_pick_cut /= in Hl.
    destruct v;simplify_eq;simpl;auto.
    destruct (decide (rc CR o c));simpl;auto.
    rewrite decide_True//.
  - intros k n v1 v2 Hv1. rewrite /inv_pick_cut /=.
    constructor. destruct v1,v2;inversion Hv1;simplify_eq =>/= //.
    rewrite H2. auto.    
Qed.

#[global] Instance cmra_morphism_pick_transform `{pick_transform_rel A} : ∀ c', CmraMorphism (inv_pick_transform c') :=
  λ c', gMapTrans_lift_CmraMorphism (inv_pick_cut c').

#[global] Instance idemp_pick_transform `{pick_transform_rel A} : ∀ c', Idemp equiv (inv_pick_transform c') :=
  λ c', gMapTrans_lift_IdemP (inv_pick_cut c').

#[global] Instance oindep_pick_transform_eq `{pick_transform_rel A} :
  ∀ c c' k, OIndep (=) (inv_pick_cut c k) (inv_pick_cut c' k).
Proof.
  intros c c' k. intros ?.
  rewrite /inv_pick_cut. simpl.
  destruct x;simpl;auto.
  destruct (decide (rc CR o c)),(decide (rc CR o c'));simpl;auto.
  - rewrite decide_True// decide_True//.
  - rewrite decide_False//.
  - rewrite decide_False//.
Qed.
#[global] Instance oindep_pick_transform_equiv `{pick_transform_rel A} :
  ∀ c c' k, OIndep (≡) (inv_pick_cut c k) (inv_pick_cut c' k).
Proof.
  intros c c' k. intros ?.
  rewrite oindep_pick_transform_eq//.
Qed.
#[global] Instance indep_pick_transform `{pick_transform_rel A} :
  ∀ c c', Indep (≡) (inv_pick_transform c) (inv_pick_transform c').
Proof.
  intros c c'.
  apply gMapTrans_lift_Indep;apply _.  
Qed.

Lemma inv_pick_cut_compose_left `{pick_transform_rel A} (c c' : C) :
  rc CR c' c ->
  ∀ l v, inv_pick_cut c' l v ≫= inv_pick_cut c l = inv_pick_cut c' l v.
Proof.
  intros Hc l v.
  rewrite /inv_pick_cut. destruct v;simpl;auto.
  case_match;simpl;auto.
  rewrite decide_True;auto.
  etrans;eauto.
Qed.
Lemma inv_pick_cut_compose_right `{pick_transform_rel A} (c c' : C) :
  rc CR c' c ->
  ∀ l v, inv_pick_cut c l v ≫= inv_pick_cut c' l = inv_pick_cut c' l v.
Proof.
  intros Hc l v.
  rewrite oindep_pick_transform_eq.
  apply inv_pick_cut_compose_left=>//.
Qed.
  
Lemma inv_pick_transform_compose_left `{pick_transform_rel A} (c c' : C) :
  rc CR c' c ->
  ∀ x, (inv_pick_transform c ∘ inv_pick_transform c') x ≡ inv_pick_transform c' x.
Proof.
  intros Hc x.
  rewrite /inv_pick_transform.
  rewrite map_entry_lift_gmap_view_compose.
  apply map_entry_lift_gmap_equiv;try apply _.
  intros l v. rewrite inv_pick_cut_compose_left//.
Qed.
Lemma inv_pick_transform_compose_right `{pick_transform_rel A} (c c' : C) :
  rc CR c' c ->
  ∀ x, (inv_pick_transform c' ∘ inv_pick_transform c) x ≡ inv_pick_transform c' x.
Proof.
  intros Hc x.
  rewrite /inv_pick_transform.
  rewrite /compose. rewrite gMapTrans_lift_Indep.
  apply inv_pick_transform_compose_left=>//.
Qed.
