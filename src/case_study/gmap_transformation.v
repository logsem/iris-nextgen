From Equations Require Import Equations.
From stdpp Require Import pmap.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.algebra Require Import gmap gmap_view view.

From self Require Import nextgen_basic gen_trans cmra_morphism_extra.

(** [mapTrans] defines a valid map transformation to be applied on a
    gmap resource algebra *)
Class mapTrans (L : Type) (V : ofe) `{EqDecision L, Countable L} :=
{
  map_trans_auth : gmap L V -> gmap L V;
  map_trans_frag : L -> V -> option V;

  map_trans_incl : forall (l : L) (v : V) (m : gmapO L V),
    m !! l = Some v -> map_trans_frag l v = map_trans_auth m !! l;

  (* The following condition states that only locations can determine
  resource discard, so that all points-to's of a location get
  discarded reguardless of fraction or value *)
  map_trans_frag_discard_all: forall (l : L) (v1 : V),
    map_trans_frag l v1 = None -> forall (v2 : V), map_trans_frag l v2 = None;
  
  map_trans_auth_ne : NonExpansive map_trans_auth;
  map_trans_frag_ne : forall k, NonExpansive (map_trans_frag k);

  (* V must be a leibniz equality *)
  v_leibniz : LeibnizEquiv V;
  v_discrete : forall (v : V), Discrete v
}.

Record ghost_mapGS (L V : Type) (Σ : gFunctors) (EqDecision0 : EqDecision L) (H : Countable L) : Set := GhostMapGS
  { ghost_map_inG : inG Σ (gmap_viewR L (leibnizO V));  ghost_name : gname }.

Fixpoint option_list_collapse_list {A : Type} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l' => a :: option_list_collapse_list l'
  | None :: l' => option_list_collapse_list l'
  end.
Definition option_list_collapse {A : Type} (l : list (option A)) : option (list A) :=
  let l' := option_list_collapse_list l in
  if bool_decide (l' = []) then None else Some l'.

Lemma option_list_collapse_id {A : Type} l : l ≠ [] -> option_list_collapse ((λ (x : A), Some x) <$> l) = Some l.
Proof.
  intros Hnil. induction l;auto;simpl. done.
  destruct l => /= //.
  assert (a0 :: l ≠ []) as Hni%IHl =>//.
  rewrite /option_list_collapse /= in Hni.
  inversion Hni. rewrite /option_list_collapse H0 /= // H0 //.
Qed.

Lemma option_list_collapse_cons_Some {A : Type} (l : list (option A)) (a : A) :
  option_list_collapse (Some a :: l) = Some (a :: option_list_collapse_list l).
Proof.
  rewrite /option_list_collapse /= //.
Qed.

Lemma option_list_collapse_cons_None {A : Type} (l : list (option A)) :
  option_list_collapse (None :: l) = option_list_collapse l.
Proof.
  rewrite /option_list_collapse /= //.
Qed.

Lemma option_list_collapse_some_eq {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> l' = option_list_collapse_list l.
Proof.
  unfold option_list_collapse. case_match;try done. intros Hl; inversion Hl. auto.
Qed.

Lemma option_list_collapse_some_nil {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> bool_decide (l' = []) = false.
Proof.
  unfold option_list_collapse. case_match;try done.
  intros Hl. inversion Hl. auto.
Qed.

Lemma option_list_collapse_some_exists {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> exists (a : A), a ∈ l' /\ (Some a) ∈ l.
Proof.
  unfold option_list_collapse. case_match;try done.
  intros Hl. inversion Hl.
  induction l;try done.
  simpl in *. case_match;simpl in *;simplify_eq.
  - exists a0. split;constructor.
  - apply IHl in H;auto.
    destruct H as [a [Hin1 Hin2]].
    exists a. split;auto. constructor;auto.
Qed.

Lemma option_list_collapse_list_length {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> length l' = length (option_list_collapse_list l).
Proof.
  revert l'; induction l;simpl =>/=l' Hl.
  - apply option_list_collapse_some_eq in Hl as -> =>//.
  - apply option_list_collapse_some_eq in Hl as ->.
    simpl. destruct a=>//.
Qed.

Lemma option_list_collapse_length {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> 0 < length l' <= length l.
Proof.
  intros Hl. split.
  { unfold option_list_collapse in Hl. case_match; try done.
    inversion Hl. apply bool_decide_eq_false in H.
    destruct (option_list_collapse_list l);try done. simpl. lia. }  
  apply option_list_collapse_some_eq in Hl;subst.
  induction l.
  - simpl. lia.
  - simpl. destruct a => /=.
    + apply le_n_S =>//.
    + constructor =>//.
Qed.

Inductive collapse_rel {A : Type} : list (option A) -> list A -> Prop :=
| collapse_nil : collapse_rel [] []
| collapse_None l l' : collapse_rel l l' -> collapse_rel (None :: l) l'
| collapse_Some l l' a : collapse_rel l l' -> collapse_rel (Some a :: l) (a :: l').
                                                          
Lemma collapse_rel_iff {A : Type} (l : list (option A)) (l' : list A) :
  collapse_rel l l' ->
  (forall x, Some x ∈ l <-> x ∈ l').
Proof.
  intros Hl. induction Hl.
  - intros x;split;intros Hcontr;inversion Hcontr.
  - intros x. split.
    + intros [Heq | Hin]%elem_of_cons;[inversion Heq|].
      apply IHHl. auto.
    + intros Hin. constructor. apply IHHl. auto.
  - intros x; split; intros [Heq|Hin]%elem_of_cons;simplify_eq;constructor.
    + apply IHHl;auto.
    + apply IHHl;auto.
Qed.

Lemma collapse_rel_witness {A : Type} (l : list (option A)) (l' : list A) :
  collapse_rel l l' ->
  (forall x, x ∈ l -> (exists x', x = Some x' /\ x' ∈ l') \/ x = None).
Proof.
  intros Hl. pose proof (collapse_rel_iff _ _ Hl).
  intros x Ha.
  destruct x;[apply H in Ha|].
  + left. intros. 
    simplify_eq. eauto.
  + by right.
Qed.

Lemma option_list_collapse_spec {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> collapse_rel l l'.
Proof.
  intros Hl. apply option_list_collapse_some_eq in Hl as ->.
  induction l.
  - simpl. constructor.
  - simpl. destruct a; constructor;auto.
Qed.

Lemma option_list_collapse_list_construct {A : Type} (l : list (option A)) (l' : list A) :
  collapse_rel l l' ->
  option_list_collapse_list l = l'.
Proof.
  intros Hl.
  induction Hl;auto.
  simpl. f_equiv. auto.
Qed.

Lemma option_list_collapse_spec_construct {A : Type} (l : list (option A)) (l' : list A) :
  bool_decide (l' = []) = false ->
  collapse_rel l l' ->
  option_list_collapse l = Some l'.
Proof.
  intros Hnil Hl.
  apply option_list_collapse_list_construct in Hl as Heq.
  rewrite /option_list_collapse Heq Hnil //.
Qed.

Lemma option_list_collapse_none_spec {A : Type} (l : list (option A)) :
  option_list_collapse l = None -> (forall x, x ∈ l -> x = None).
Proof.
  induction l =>Hnone x Hin.
  - inversion Hin.
  - apply elem_of_cons in Hin as [Heq|Hin].
    + subst. destruct a;auto.
      rewrite /option_list_collapse /= in Hnone.
      done.
    + destruct a;auto.
      rewrite /option_list_collapse /= in Hnone.
      done.
Qed.

Lemma option_list_collapse_none_construct {A : Type} (l : list (option A)) :
   (forall x, x ∈ l -> x = None) ->
  option_list_collapse l = None.
Proof.
  induction l;simpl;auto.
  intros Hcond.
  rewrite /option_list_collapse /=.
  rewrite (Hcond a);[|constructor].
  case_match;auto.
  assert (option_list_collapse l = None) as Hnone.
  { apply IHl. intros. apply Hcond. constructor. auto. }
  rewrite /option_list_collapse H in Hnone. auto.
Qed.

Lemma option_list_collapse_list_app {A : Type} (l l2 : list (option A)) :
  option_list_collapse_list (l ++ l2) = option_list_collapse_list l ++ option_list_collapse_list l2.
Proof.
  revert l2;induction l =>l2 /= //.
  destruct a;auto.
  simpl. f_equiv. apply IHl.
Qed.

Lemma option_list_collapse_some_some_app {A : Type} (l1 l2 : list (option A)) (l1' l2' : list A) :
  option_list_collapse l1 = Some l1' ->
  option_list_collapse l2 = Some l2' ->
  option_list_collapse (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  intros Hl1 Hl2.
  apply option_list_collapse_spec in Hl1 as Hspec.
  induction Hspec;auto.
  rewrite option_list_collapse_cons_Some in Hl1. simplify_eq.
  simpl. rewrite /option_list_collapse /=. f_equiv. f_equiv.
  apply option_list_collapse_some_eq in Hl2;subst.
  apply option_list_collapse_list_app.
Qed.

Lemma option_list_collapse_none_l_app {A : Type} (l1 l2 : list (option A)) res :
  option_list_collapse l1 = None ->
  option_list_collapse l2 = res ->
  option_list_collapse (l1 ++ l2) = res.
Proof.
  revert l2 res. induction l1;intros l2 res Hl1 Hres;auto.
  simpl. rewrite /option_list_collapse /=. destruct a => // /=.
  rewrite option_list_collapse_cons_None in Hl1. apply IHl1 in Hres =>//.
Qed.

Lemma option_list_collapse_none_r_app {A : Type} (l1 l2 : list (option A)) res :
  option_list_collapse l1 = res ->
  option_list_collapse l2 = None ->
  option_list_collapse (l1 ++ l2) = res.
Proof.
  revert l2 res. induction l1;intros l2 res Hl1 Hres;auto.
  - simpl. rewrite /option_list_collapse /= in Hl1. subst. auto.
  - simpl. destruct a.
    + rewrite option_list_collapse_cons_Some in Hl1; simplify_eq.
      eapply IHl1 in Hres;eauto.
      rewrite /option_list_collapse /=. f_equiv. f_equiv.
      rewrite /option_list_collapse in Hres.
      case_match;case_match;simplify_eq;try done.
      apply bool_decide_eq_true in H as ->.
      apply bool_decide_eq_true in H0 as ->. auto.
    + rewrite option_list_collapse_cons_None.
      rewrite option_list_collapse_cons_None in Hl1.
      apply IHl1;auto.
Qed.
  
Definition agree_option_list_map {A B} (f : A → option B) (x : agree A) : option (list B) :=
  option_list_collapse (f <$> x.(agree_car)).
Program Definition lift_option_map {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false)
  : option (agree A) :=
  match x with
  | Some agree_car' => Some {| agree_car := agree_car' ; agree_not_nil := _ |}
  | None => None
  end.
Next Obligation.
  intros. destruct x;simplify_eq. auto.
Qed.
  
Lemma agree_option_eq_some_1 {A} (x : option (list A)) (y : agree A) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  x = Some (agree_car y) → lift_option_map x Hne = Some y.
Proof.
  intros Hx. destruct x;[|done]. simplify_eq. simpl.
  f_equal. destruct y as [b ?]; simpl. f_equal. apply proof_irrel.
Qed.
Lemma agree_option_eq_some_2 {A} (x : option (list A)) (y : agree A) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  lift_option_map x Hne = Some y -> x = Some (agree_car y).
Proof.
  intros Hx. destruct x;[|done]. simpl in *. simplify_eq. simpl. auto.
Qed.
Lemma agree_option_eq_some {A} (x : option (list A)) (y : agree A) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  x = Some (agree_car y) <-> lift_option_map x Hne = Some y.
Proof. split. apply agree_option_eq_some_1. apply agree_option_eq_some_2. Qed.

Lemma agree_option_eq_none_1 {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  x = None → lift_option_map x Hne = None.
Proof.
  intros Hx. destruct x;[|done]. simplify_eq.
Qed.
Lemma agree_option_eq_none_2 {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  lift_option_map x Hne = None -> x = None.
Proof.
  intros Hx. destruct x;[|done]. simplify_eq.
Qed.
Lemma agree_option_eq_none {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  lift_option_map x Hne = None <-> x = None.
Proof. split. apply agree_option_eq_none_2. apply agree_option_eq_none_1. Qed.


Program Definition agree_option_map {A B} (f : A → option B) (x : agree A) : option (agree B) :=
  lift_option_map (option_list_collapse (f <$> x.(agree_car))) _.
Next Obligation.
  intros A B f [[|??] ?] ? Hsome%option_list_collapse_some_nil =>//.
Qed.

Lemma option_map_list_collapse_None {A: Type} (l : list A) :
  bool_decide (l = []) = false ->
  option_list_collapse ((λ x : A, Some x) <$> l) = None -> False.
Proof.
  induction l;simpl;[done|].
  intros _ Hnone. rewrite option_list_collapse_cons_Some in Hnone. done. 
Qed.

Lemma agree_option_map_id {A} (x : agree A) : bool_decide (agree_car x = []) = false -> agree_option_map (λ x, Some x) x = Some x.
Proof.
  intros Hnil.
  apply agree_option_eq_some. apply option_list_collapse_id.
  apply bool_decide_eq_false in Hnil. auto. 
Qed.

Lemma collapse_rel_compose {A B C : Type} (f : A -> option B) (g : B -> option C) l1 l2 l3:
  collapse_rel (f <$> l1) l2 ->
  collapse_rel (g <$> l2) l3 ->
  collapse_rel ((λ x : A, f x ≫= g) <$> l1) l3.
Proof.
  revert l2 l3.
  induction l1 => l2 l3 Hl1 Hl2.
  - inversion Hl1;subst.
    simpl. inversion Hl2;subst;auto.
  - simpl in *. inversion Hl1;subst;simplify_eq.
    + simpl. 
      constructor. eapply IHl1;eauto.
    + simpl in *.
      destruct (g a0).
      * inversion Hl2;subst. constructor.
        eapply IHl1;eauto.
      * constructor. eapply IHl1;eauto. inversion Hl2;auto.
Qed.


      
Lemma agree_option_map_compose {A B C} (f : A → option B) (g : B → option C) (x : agree A) :
  agree_option_map (λ x, f x ≫= g) x = agree_option_map f x ≫= agree_option_map g.
Proof.
  destruct (agree_option_map f x) eqn:Hf; simpl.
  - apply agree_option_eq_some in Hf.
    destruct (agree_option_map g a) eqn:Hg; simpl.
    + apply agree_option_eq_some in Hg.
      apply agree_option_eq_some.
      pose proof (option_list_collapse_spec _ _ Hf) as Hspec1.
      pose proof (option_list_collapse_spec _ _ Hg) as Hspec2.
      apply option_list_collapse_spec_construct.
      { destruct a0. auto. }
      eapply collapse_rel_compose;eauto.
    + apply agree_option_eq_none in Hg as Hnone.
      apply option_list_collapse_length in Hf as Hlen. destruct Hlen as [Hlt Hle].
      apply agree_option_eq_none.
      apply option_list_collapse_none_construct.
      apply option_list_collapse_spec in Hf.
      intros x' Hin. apply elem_of_list_fmap in Hin as [y [Heq Hin]].
      destruct (f y) eqn:Hy;simpl in *;subst;auto.
      eapply option_list_collapse_none_spec;eauto. apply elem_of_list_fmap.
      eexists;split;eauto.
      eapply collapse_rel_iff;eauto. rewrite -Hy.
      apply elem_of_list_fmap. eexists;split;eauto.
  - apply agree_option_eq_none.
    apply agree_option_eq_none in Hf.
    apply option_list_collapse_none_construct.
    intros x' [y [Heq Hin]]%elem_of_list_fmap.
    destruct (f y) eqn:Hy;simpl in *;auto.
    subst. 
    eapply option_list_collapse_none_spec with (x:=f y) in Hf;eauto;simplify_eq.
    apply elem_of_list_fmap;eauto.
Qed.

Lemma agree_option_map_to_agree {A B} (f : A → option B) (x : A) :
  agree_option_map f (to_agree x) = (f x) ≫= (λ x, Some (to_agree x)).
Proof.
  destruct (f x) eqn:Hf.
  - simpl. apply agree_option_eq_some.
    rewrite /= Hf //.
  - simpl. apply agree_option_eq_none.
    rewrite /= Hf //.
Qed.

Section agree_option_map.
  Context {A B : ofe} (f : A → option B) {Hf: NonExpansive f}.

  Local Instance agree_option_map_ne : NonExpansive (agree_option_map f).
  Proof using Type*.
    intros n x y [H H'].
    destruct (agree_option_map f x) eqn:Hx, (agree_option_map f y) eqn:Hy;auto.
    - f_equiv. apply agree_option_eq_some in Hx.
      apply agree_option_eq_some in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec2.
      apply option_list_collapse_length in Hx as Hlen.
      apply option_list_collapse_length in Hy as Hlen'.
      rewrite fmap_length in Hlen; rewrite fmap_length in Hlen'.
      split=> b /=; setoid_rewrite elem_of_list_lookup.
      + rewrite -!elem_of_list_lookup. intros Hi.
        apply collapse_rel_iff with (x:=b) in Hspec1 as Hiff.
        apply Hiff in Hi.
        apply elem_of_list_fmap in Hi as [c [Heq Hc]];simplify_eq.
        apply H in Hc as [c' [Hin Hc']].
        apply Hf in Hc'. rewrite -Heq in Hc'.
        apply elem_of_list_fmap_1 with (f:=f) in Hin.
        destruct (f c') eqn:Hfc;inversion Hc'; subst.
        apply collapse_rel_iff with (x:=o) in Hspec2 as Hiff2.
        apply Hiff2 in Hin. exists o. rewrite -elem_of_list_lookup. split;auto.
      + rewrite -!elem_of_list_lookup. intros Hi.
        apply collapse_rel_iff with (x:=b) in Hspec2 as Hiff.
        apply Hiff in Hi.
        apply elem_of_list_fmap in Hi as [c [Heq Hc]];simplify_eq.
        apply H' in Hc as [c' [Hin Hc']].
        apply Hf in Hc'. rewrite -Heq in Hc'.
        apply elem_of_list_fmap_1 with (f:=f) in Hin.
        destruct (f c') eqn:Hfc;inversion Hc'; subst.
        apply collapse_rel_iff with (x:=o) in Hspec1 as Hiff1.
        apply Hiff1 in Hin. exists o. rewrite -elem_of_list_lookup. split;auto.
    - apply agree_option_eq_some in Hx.
      apply agree_option_eq_none in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hy) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff in Hb. apply elem_of_list_fmap in Hb as [b' [Heq Hb']].
      apply H in Hb' as Hin. destruct Hin as [c [Hin Hne]].
      apply Hf in Hne. apply elem_of_list_fmap_1 with (f:=f) in Hin.
      apply Hspec2 in Hin as Heq'. rewrite -Heq Heq' in Hne. inversion Hne.
    - apply agree_option_eq_none in Hx.
      apply agree_option_eq_some in Hy.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hx) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff in Hb. apply elem_of_list_fmap in Hb as [b' [Heq Hb']].
      apply H' in Hb' as Hin. destruct Hin as [c [Hin Hne]].
      apply Hf in Hne. apply elem_of_list_fmap_1 with (f:=f) in Hin.
      apply Hspec2 in Hin as Heq'. rewrite -Heq Heq' in Hne. inversion Hne.
  Qed.
  Local Instance agree_option_map_proper : Proper ((≡) ==> (≡)) (agree_option_map f) := ne_proper _.

  Lemma agree_option_map_ext (g : A → option B) x :
    (∀ a, f a ≡ g a) → agree_option_map f x ≡ agree_option_map g x.
  Proof using Hf.
    intros Hfg.
    destruct (agree_option_map f x) eqn:Hx, (agree_option_map g x) eqn:Hy;auto.
    - f_equiv. apply agree_option_eq_some in Hx.
      apply agree_option_eq_some in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
      pose proof (collapse_rel_iff _ _ Hspec2) as Hiff2.
      intros n.
      split=> b /=; setoid_rewrite elem_of_list_lookup.
      + rewrite -elem_of_list_lookup.
        intros Hb.
        apply Hiff1 in Hb as Hin.
        apply elem_of_list_fmap in Hin as [c [Heq Hc]].
        apply elem_of_list_fmap_1 with (f:=g) in Hc as Hc'.
        pose proof (Hfg c) as Hequiv. rewrite -Heq in Hequiv.
        destruct (g c) eqn:Hsome;[|inversion Hequiv].
        apply Hiff2 in Hc'. exists o. rewrite -elem_of_list_lookup. split;eauto.
        inversion Hequiv;subst;auto.
      + rewrite -elem_of_list_lookup.
        intros Hb.
        apply Hiff2 in Hb as Hin.
        apply elem_of_list_fmap in Hin as [c [Heq Hc]].
        apply elem_of_list_fmap_1 with (f:=f) in Hc as Hc'.
        pose proof (Hfg c) as Hequiv. rewrite -Heq in Hequiv.
        destruct (f c) eqn:Hsome;[|inversion Hequiv].
        apply Hiff1 in Hc'. exists o. rewrite -elem_of_list_lookup. split;eauto.
        inversion Hequiv;subst;auto.
    - apply agree_option_eq_some in Hx.
      apply agree_option_eq_none in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hy) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff1 in Hb.
      apply elem_of_list_fmap in Hb as [y [Heq Hin]].
      apply elem_of_list_fmap_1 with (f:=g) in Hin.
      apply Hspec2 in Hin. specialize (Hfg y).
      rewrite -Heq Hin in Hfg. inversion Hfg.
    - apply agree_option_eq_some in Hy.
      apply agree_option_eq_none in Hx.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hx) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff1 in Hb.
      apply elem_of_list_fmap in Hb as [y [Heq Hin]].
      apply elem_of_list_fmap_1 with (f:=f) in Hin.
      apply Hspec2 in Hin. specialize (Hfg y).
      rewrite -Heq Hin in Hfg. inversion Hfg.
  Qed.

  Lemma agree_option_map_validN x n :
    ✓{n} x -> ✓{n} agree_option_map f x.
  Proof.
    intros Hv.
    destruct (agree_option_map f x) eqn:Hx;cycle 1.
    { rewrite /validN /cmra_validN /= //. }
    rename a into x'.
    apply agree_option_eq_some in Hx.
    pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
    rewrite agree_validN_def in Hv.
    apply agree_validN_def.
    intros a b Ha Hb.
    pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
    apply Hiff1 in Ha as Ha'.
    apply Hiff1 in Hb as Hb'.
    apply elem_of_list_fmap in Ha' as [a' [Heq1 Ha']].
    apply elem_of_list_fmap in Hb' as [b' [Heq2 Hb']].
    eapply Hv in Ha';eauto. apply Hf in Ha'. rewrite -Heq1 -Heq2 in Ha'.
    inversion Ha';auto.
  Qed.

  Lemma agree_option_map_op v1 v2 :
    agree_option_map f (v1 ⋅ v2) = agree_option_map f v1 ⋅ agree_option_map f v2.
  Proof.
    destruct (agree_option_map f v1) eqn:Hv1.
    - apply agree_option_eq_some in Hv1.
      destruct (agree_option_map f v2) eqn:Hv2. 
      + apply agree_option_eq_some in Hv2.
        destruct a,a0;simpl in *. rewrite -Some_op.
        destruct (agree_option_map f (v1 ⋅ v2)) eqn:Hv;cycle 1.
        { exfalso. apply agree_option_eq_none in Hv.
          rewrite fmap_app in Hv.
          by erewrite option_list_collapse_some_some_app in Hv;eauto. }
        apply agree_option_eq_some in Hv.
        rewrite fmap_app in Hv.
        erewrite option_list_collapse_some_some_app in Hv;eauto.
        simplify_eq. destruct a;simpl in *. cbv. rewrite -/app.
        f_equal. apply agree_eq. simpl. auto.
      + apply agree_option_eq_none in Hv2.
        destruct a;simpl in *. rewrite op_None_right_id.
        destruct (agree_option_map f (v1 ⋅ v2)) eqn:Hv;cycle 1.
        { exfalso. apply agree_option_eq_none in Hv.
          rewrite fmap_app in Hv.
          by erewrite option_list_collapse_none_r_app in Hv;eauto. }
        apply agree_option_eq_some in Hv.
        rewrite fmap_app in Hv.
        erewrite option_list_collapse_none_r_app in Hv;eauto.
        simplify_eq. destruct a;simpl in *. f_equal. apply agree_eq.
        simpl. auto.
    - apply agree_option_eq_none in Hv1.
      destruct (agree_option_map f (v1 ⋅ v2)) eqn:Hv;cycle 1.
      { apply agree_option_eq_none in Hv.
        rewrite fmap_app in Hv.
        erewrite option_list_collapse_none_l_app in Hv;eauto.
        symmetry. rewrite op_None_left_id. apply agree_option_eq_none.
        auto. }
      apply agree_option_eq_some in Hv.
      rewrite fmap_app in Hv.
      erewrite option_list_collapse_none_l_app in Hv;eauto.
      symmetry. rewrite op_None_left_id. apply agree_option_eq_some.
      auto.
  Qed.
        
End agree_option_map.

Definition map_trans_frag_lift {L : Type} {V : ofe} `{EqDecision L, Countable L} (f : L -> V -> option V) :
  L -> prodR dfracR (agreeR V) -> option (prodR dfracR (agreeR V)) :=
  λ l dv, let '(d,v) := dv in agree_option_map (f l) v ≫= λ v', Some (d,v').

Definition gmapTrans_auth_lift {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  (gt : mapTrans K V) : gmapO K V -> gmapO K V := map_trans_auth.

Definition gmapTrans_frag_lift {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  (gt : mapTrans K V) : (gmap_view.gmap_view_fragUR K V) → (gmap_view.gmap_view_fragUR K V) :=
  λ frag_view, map_imap (map_trans_frag_lift gt.(map_trans_frag)) frag_view.


Definition gmapTrans_lift {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  (gt : mapTrans K V) : gmap_viewR K (V) -> gmap_viewR K (V) := fmap_view (gmapTrans_auth_lift gt) (gmapTrans_frag_lift gt).



Global Instance gmap_map_imap_ne {K : Type} {A B : ofe} `{EqDecision K, Countable K}
  (f : K -> (prodR dfracR (agreeR A)) -> option (prodR dfracR (agreeR B))) :
  (forall k, NonExpansive (f k)) -> NonExpansive (λ (m1 : gmap_view.gmap_view_fragUR K A), (map_imap f m1) : gmap_view.gmap_view_fragUR K B).
Proof.
  intros Hf n m1 m2 Hne. intros k.
  rewrite !map_lookup_imap. pose proof (Hne k) as Hlook. rewrite Hlook. auto.
Qed.

Lemma to_agree_dist {V : ofe} n (w' : agree V) (w : V) :
  w' ≡{n}≡ to_agree w <-> forall a, a ∈ agree_car w' -> a ≡{n}≡ w.
Proof.
  split.
  - intros Hne. inversion Hne as [Hin1 Hin2].
    intros a Hin. apply Hin1 in Hin as [b [Hb Heq]].
    unfold to_agree in Hb. simpl in *.
    apply elem_of_list_singleton in Hb;subst.
    auto.
  - intros Hcond. split.
    + intros. 
      apply Hcond in H. exists w. split;auto.
      rewrite /to_agree /=. constructor.
    + rewrite /to_agree /=. intros v H%elem_of_list_singleton;subst.
      pose proof (elem_of_agree w') as [a Ha].
      exists a. split;auto.
Qed.    

Lemma dist_to_agree_validN {A : ofe} (n : nat) (x : agree A) (a : A) : x ≡{n}≡ to_agree a -> ✓{n} x.
Proof.
  intros.
  apply agree_validN_def. intros.
  rewrite to_agree_dist in H. apply H in H0.
  apply H in H1. rewrite H0. auto.
Qed.

Lemma map_trans_auth_frag_rel {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K} (gt : mapTrans K V) (n : nat)
  (m1 : gmap K V) (view_frag_proj : gmap_view.gmap_view_fragUR K V) :
  gmap_view.gmap_view_rel_raw K V n m1 view_frag_proj ->
  gmap_view.gmap_view_rel_raw K V n (map_trans_auth m1) (map_imap (map_trans_frag_lift map_trans_frag) view_frag_proj).
Proof.
  intros Hv2. intros i [d' a'] Hlook1. simpl.
  rewrite map_lookup_imap in Hlook1.
  destruct (view_frag_proj !! i) eqn:Hlook2;rewrite Hlook2 /= in Hlook1;[|done].
  destruct c as [q w'];simpl in *.
  destruct (agree_option_map (map_trans_frag i) w') eqn:Hsome;simpl in *;simplify_eq.
  destruct (Hv2 i (d',w') Hlook2) as [w [Hag [Hd Hw]]];simpl in *.
  apply dist_to_agree_validN in Hag as Hval.
  apply agree_option_map_validN with (f:=map_trans_frag i) in Hval as Hval';eauto;[|apply gt.(map_trans_frag_ne)].
  rewrite Hsome in Hval'. rewrite Some_validN in Hval'.
  apply agree_option_eq_some in Hsome.
  apply option_list_collapse_spec in Hsome as Hspec.
  pose proof (collapse_rel_iff _ _ Hspec) as Hiff.
  apply map_trans_incl in Hw as Heq.
  pose proof (elem_of_agree w') as [e Hin].
  assert (e = w) as ->.
  { rewrite to_agree_dist in Hag. apply Hag in Hin. eauto.
    apply v_leibniz. apply discrete_iff in Hin;auto.
    apply v_discrete. }
  apply elem_of_list_fmap_1 with (f:=map_trans_frag i) in Hin.
  destruct (map_trans_auth m1 !! i) eqn:Hres.
  - rewrite Heq in Hin. apply Hiff in Hin.
    apply to_agree_uninjN in Hval' as Hb; destruct Hb as [b Hb].
    symmetry in Hb. rewrite to_agree_dist in Hb.
    apply Hb in Hin. exists o. split;auto.
    apply to_agree_dist. intros. rewrite Hin. auto.
  - apply option_list_collapse_some_exists in Hsome as Ha.
    destruct Ha as [a [Hina HH]].
    apply elem_of_list_fmap in HH as [y [Heq' Hy]].
    rewrite Heq in Hin.
    apply elem_of_list_fmap in Hin as [y' [Heq'' Hnone]].
    rewrite agree_validN_def in Hval.
    eapply Hval in Hnone;[|apply Hy].
    assert (y = y') as ->.
    { apply v_leibniz. apply discrete_iff in Hnone;auto. apply v_discrete. }
    rewrite -Heq' in Heq''. done.
Qed.

Lemma agree_option_map_discard_all {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K} (gt : mapTrans K V)
  (i : K) (v1 v2 a : agree V):
  agree_option_map (map_trans_frag i) v1 = Some a ->
  agree_option_map (map_trans_frag i) v2 = None -> False.
Proof.
  intros Hag1 Hag2.
  apply agree_option_eq_some in Hag1.
  apply agree_option_eq_none in Hag2.
  pose proof (elem_of_agree v2) as [v Hv].
  pose proof (map_trans_frag_discard_all i v).
  pose proof (option_list_collapse_none_spec _ Hag2) as Hspec2.
  apply elem_of_list_fmap_1 with (f:=map_trans_frag i) in Hv.
  apply Hspec2 in Hv. pose proof (H Hv).
  pose proof (option_list_collapse_spec _ _ Hag1) as Hspec1.
  pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
  pose proof (elem_of_agree a) as [a0 Ha0].
  apply Hiff1 in Ha0.
  apply elem_of_list_fmap in Ha0 as [? [Hcontr ?]].
  rewrite H0 in Hcontr. done.
Qed.
  
Global Instance gmapTrans_frag_lift_CmraMorphism {K : Type} (V : ofe) (eqK : EqDecision K) {countK : Countable K}
  (gt : mapTrans K V) :  CmraMorphism (gmapTrans_frag_lift gt).
Proof.
  split.
  - intros n x y Hne.
    destruct x,y =>/=.
    apply gmap_map_imap_ne =>//.
    intros k m [d1 v1] [d2 v2] Hne2. simpl. inversion Hne2 as [Hne1 Hne2'];simpl in *; simplify_eq.
    apply option_mbind_ne.
    + intros a1 a2 Ha. constructor. split;auto.
    + apply agree_option_map_ne =>//. apply gt.(map_trans_frag_ne).
  - intros n x Hx i.
    specialize (Hx i).
    rewrite /gmapTrans_frag_lift map_lookup_imap.
    destruct (x !! i) eqn:Hsome;[|rewrite Hsome //].
    rewrite Hsome in Hx. rewrite Hsome /=.
    rewrite Some_validN in Hx. inversion Hx as [Hx1 Hx2].
    destruct c as [q v]; simpl in *.
    destruct (agree_option_map (map_trans_frag i) v) eqn:Hv =>// /=.
    apply Some_validN. split => // /=. rewrite -Some_validN -Hv.
    apply agree_option_map_validN =>//. apply map_trans_frag_ne.
  - intros view_frag_proj. rewrite /gmapTrans_frag_lift /=.
    rewrite !cmra_pcore_core. f_equiv.
    intros i.
    rewrite map_lookup_imap.
    destruct (core view_frag_proj !! i) eqn:Hlook;rewrite Hlook => /=.
    * destruct c as [d v];simpl in *.
      rewrite lookup_core in Hlook. rewrite lookup_core.
      unfold map_trans_frag_lift.
      destruct (view_frag_proj !! i) eqn:Hi; rewrite Hi in Hlook;[|inversion Hlook].
      destruct c as [d' v'].
      rewrite map_lookup_imap Hi /=.
      assert (v = v') as ->.
      { destruct d,d'; inversion Hlook;auto. }
      destruct (agree_option_map (map_trans_frag i) v') eqn:Hv1 => /= //.
      destruct d,d';auto;inversion Hlook.
    * rewrite lookup_core in Hlook.
      destruct (view_frag_proj !! i) eqn:Hi;rewrite Hi in Hlook.
      { destruct c as [d v];simpl in *. destruct d;inversion Hlook.
        rewrite lookup_core map_lookup_imap Hi /=.
        destruct (agree_option_map (map_trans_frag i) v) =>//. }
      { rewrite lookup_core map_lookup_imap Hi /= //. }
  - intros view_frag_proj view_frag_proj0.
    intros i.
    rewrite !lookup_op !map_lookup_imap. rewrite lookup_op.
    destruct (view_frag_proj !! i) eqn:Hlook1,(view_frag_proj0 !! i) eqn:Hlook2;rewrite Hlook1 Hlook2; simpl in *=>//.
    * destruct c as [d1 v1],c0 as [d2 v2];simpl in *.
      rewrite agree_option_map_op.
      destruct (agree_option_map (map_trans_frag i) v1) eqn:Hag1, (agree_option_map (map_trans_frag i) v2) eqn:Hag2;simpl in *;auto.
      ** exfalso. eapply agree_option_map_discard_all;eauto.
      ** exfalso. eapply agree_option_map_discard_all;eauto.
    * rewrite op_None_right_id. auto.
    * rewrite op_None_left_id. auto.
Qed.      

Global Instance gmapTrans_lift_CmraMorphism {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  (gt : mapTrans K V) : CmraMorphism (gmapTrans_lift gt).
Proof.
  apply fmap_view_cmra_morphism.
  - apply map_trans_auth_ne.
  - apply gmapTrans_frag_lift_CmraMorphism.
  - intros. apply map_trans_auth_frag_rel. auto.
Qed.
