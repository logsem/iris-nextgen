From stdpp Require Import fin_maps.
From iris.algebra Require Import gmap.
From nextgen Require Import nextgen_basic gen_trans gmap_view_transformation.
From nextgen.case_study Require Export stack_lang.
Set Default Proof Using "Type".


Fixpoint list_to_gmap_stack_fix (s : list (gmap loc val)) (i : nat) : gmap nat (gmap loc val) :=
  match s with
  | [] => ∅
  | si :: s' => <[i:=si]> (list_to_gmap_stack_fix s' (S i))
  end.
Definition list_to_gmap_stack (s : list (gmap loc val)) : gmap (nat * loc) val :=
  gmap_uncurry (list_to_gmap_stack_fix s 0).

Lemma gmap_uncurry_insert_empty {K1 K2 V : Type} `{EqDecision K1,Countable K1,EqDecision K2,Countable K2}
  (m : gmap K1 (gmap K2 V)) (k : K1) :
  m !! k = None ->
  gmap_uncurry (<[k := ∅]> m) = gmap_uncurry m.
Proof.
  intros Hnone. apply map_eq. intros [k1 k2].
  rewrite !lookup_gmap_uncurry.
  destruct (decide (k1 = k)).
  - subst. rewrite lookup_insert Hnone. simpl. auto.
  - rewrite lookup_insert_ne//.
Qed.

Lemma list_to_gmap_stack_push_stack s :
  list_to_gmap_stack (push_stack s) = list_to_gmap_stack s.
Proof.
  rewrite /list_to_gmap_stack /push_stack /list_to_gmap_stack_fix.
  generalize 0. induction s;intros n; simpl;auto.
  - rewrite gmap_uncurry_insert_empty//.
  - rewrite -/list_to_gmap_stack_fix.
    rewrite -/list_to_gmap_stack_fix in IHs.
    apply map_eq. intros [i l].
    rewrite !lookup_gmap_uncurry.
    destruct (decide (i = n)).
    + subst. rewrite !lookup_insert. auto.
    + rewrite !lookup_insert_ne//.
      specialize (IHs (S n)).
      rewrite - lookup_gmap_uncurry IHs lookup_gmap_uncurry //.
Qed.

Lemma push_stack_length s :
  length (push_stack s) = S (length s).
Proof. induction s; simpl; auto. Qed.

Lemma list_to_gmap_stack_fix_lookup_is_Some s n m :
  is_Some (list_to_gmap_stack_fix s n !! m) ->
  m < length s + n.
Proof.
  revert n m; induction s;intros n m.
  - simpl. intros [? ?];done.
  - simpl. intros Hx.
    destruct (decide (n = m));subst.
    + simplify_map_eq. lia.
    + rewrite lookup_insert_ne// in Hx.
      apply IHs in Hx. lia.
Qed.
Lemma list_to_gmap_stack_fix_lookup_Some s n m v :
  list_to_gmap_stack_fix s n !! m = Some v ->
  m < length s + n.
Proof.
  intros Hsome.
  apply list_to_gmap_stack_fix_lookup_is_Some.
  eauto.
Qed.

Lemma list_to_gmap_stack_lookup_is_Some s m l :
  is_Some (list_to_gmap_stack s !! (m, l)) ->
  m < length s.
Proof.
  intros [x Hx].
  unfold list_to_gmap_stack in Hx.
  rewrite lookup_gmap_uncurry in Hx.
  destruct (list_to_gmap_stack_fix s 0 !! m) eqn:Hsome;try done.
  apply list_to_gmap_stack_fix_lookup_Some in Hsome. lia.
Qed.
Lemma list_to_gmap_stack_lookup_Some s m l v :
  list_to_gmap_stack s !! (m, l) = Some v ->
  m < length s.
Proof.
  intros Hsome.
  eapply list_to_gmap_stack_lookup_is_Some;eauto.
Qed.

Lemma list_to_gmap_stack_fix_snoc_mid s x n :
  (list_to_gmap_stack_fix (s ++ [x]) n) = <[n + (length s) := x]> (list_to_gmap_stack_fix s n).
Proof.
  revert n. induction s;intros n.
  - rewrite app_nil_l /= PeanoNat.Nat.add_0_r. auto.
  - simpl.  rewrite IHs. rewrite insert_commute;[|lia].
    assert (S n + length s = n + S (length s)) as ->;[lia|].
    auto.
Qed.

Lemma list_to_gmap_stack_fix_snoc s x :
  (list_to_gmap_stack_fix (s ++ [x]) 0) = <[(length s) := x]> (list_to_gmap_stack_fix s 0).
Proof.
  assert (length s = 0 + length s) as ->;[lia|].
  apply list_to_gmap_stack_fix_snoc_mid.
Qed.

Lemma list_to_gmap_lookup_snoc s x m l :
  m < length s ->
  list_to_gmap_stack (s ++ [x]) !! (m, l) = list_to_gmap_stack s !! (m, l).
Proof.
  revert m. induction s using rev_ind;intros m Hle.
  - simpl in *. destruct m;lia.
  - destruct (decide (m = length s)).
    + subst. rewrite /list_to_gmap_stack /= !lookup_gmap_uncurry.
      rewrite list_to_gmap_stack_fix_snoc. rewrite app_length /=.
      rewrite lookup_insert_ne//. lia.
    + rewrite app_length /= in Hle. assert (m < length s) as Hlt;[lia|].
      apply IHs in Hlt.
      rewrite /list_to_gmap_stack /= !lookup_gmap_uncurry.
      rewrite list_to_gmap_stack_fix_snoc.
      rewrite lookup_insert_ne;[|rewrite app_length;lia].
      rewrite /list_to_gmap_stack /= !lookup_gmap_uncurry in Hlt.
      auto.
Qed.

Lemma list_to_gmap_stack_fix_lookup s n m l :
  n <= m ->
  list_to_gmap_stack_fix s n !! m ≫= lookup l = s !! (m - n) ≫= (λ σ : gmap loc val, σ !! l).
Proof.
  revert n. induction s;intros n Hle.
  - simpl. auto.
  - simpl. destruct (decide (n = m)).
    + subst. rewrite lookup_insert Nat.sub_diag /= //.
    + assert (S n <= m);[lia|].
      rewrite lookup_insert_ne // IHs //.
      assert (m - n = S (m - S n)) as ->;[lia|].
      simpl. auto.
Qed.    

Lemma list_to_gmap_stack_lookup (s : list (gmap loc val)) (m : nat) (l : loc) :
  (list_to_gmap_stack s) !! (m, l) = s !! m ≫= λ σ, σ !! l.
Proof.
  rewrite /list_to_gmap_stack.
  rewrite lookup_gmap_uncurry.
  rewrite list_to_gmap_stack_fix_lookup;[|lia].
  rewrite Nat.sub_0_r. auto.
Qed.

Lemma list_to_gmap_stack_insert s s0 l v n :
  s !! n = Some s0 ->
  <[(n, l) := v]> (list_to_gmap_stack s) = list_to_gmap_stack (<[n :=<[l:=v]>s0]> s).
Proof.
  intros Hl. apply map_eq.
  intros [n' l'].
  rewrite list_to_gmap_stack_lookup.
  apply lookup_lt_Some in Hl as Hlt.
  destruct (decide ((n',l') = (n, l))).
  - simplify_eq.
    rewrite lookup_insert list_lookup_insert// /=.
    rewrite lookup_insert //.
  - rewrite lookup_insert_ne//.
    rewrite list_to_gmap_stack_lookup.
    destruct (decide (n' = n)).
    + subst. rewrite list_lookup_insert// Hl /=.
      rewrite lookup_insert_ne//. intros Hcontr;subst. done.
    + rewrite list_lookup_insert_ne//.
Qed.

Section pop_func.

  Definition stackM := gmap_view.gmap_viewUR (nat * loc) (leibnizO val).

  Definition stack_cond (n : nat) : ((nat * loc) * (leibnizO val)) -> Prop := (λ kv : ((nat * loc) * (leibnizO val)), kv.1.1 < n).
  Global Instance stack_cut_cond_dec (n : nat) : forall (x : ((nat * loc) * (leibnizO val))), Decision (stack_cond n x).
  Proof. intros. unfold stack_cond. apply _. Qed.

  Definition stack_cut (n : nat) (m : gmapO (nat * loc) (leibnizO val)) : gmapO (nat * loc) (leibnizO val) :=
    filter (stack_cond n) m.

  Definition stack_location_cut (n : nat) (nl : nat * loc) (v : leibnizO val) :=
    if (bool_decide (stack_cond n (nl,v))) then Some v else None.

  Lemma stack_map_trans_incl (n : nat) : forall (l : nat * loc) (v : leibnizO val) (m : gmapO (nat * loc) (leibnizO val)),
      m !! l = Some v -> (stack_location_cut n) l v = (stack_cut n) m !! l.
  Proof.
    intros l v m Hl.
    destruct (stack_cut n m !! l) eqn:Hm;unfold stack_cut in Hm.
    - rewrite map_filter_lookup_Some in Hm.
      destruct Hm as [Ho Hcond].
      rewrite /stack_location_cut bool_decide_true // -Hl -Ho //.
    - rewrite map_filter_lookup_None in Hm. destruct Hm as [Hcontr | Hcond].
      + rewrite Hl in Hcontr. done.
      + apply Hcond in Hl.
        rewrite /stack_location_cut bool_decide_false //.
  Qed.

  Lemma stack_map_trans_frag_discard_all (n : nat) : forall (l : nat * loc) (v1 : leibnizO val),
      (stack_location_cut n) l v1 = None -> forall (v2 : leibnizO val), (stack_location_cut n) l v2 = None.
  Proof.
    rewrite /stack_location_cut.
    intros l v1 Hl v2.
    case_match;try done.
    rewrite /stack_cond /= in H.
    rewrite /stack_cond /=.
    apply bool_decide_eq_false in H.
    rewrite bool_decide_false//.
  Qed.

  Global Instance stack_cut_ne (n : nat) : (NonExpansive (stack_cut n)).
  Proof. 
    unfold stack_cut. intros i m1 m2 Hi.
    assert (LeibnizEquiv (leibnizO val)) as Hleib;[apply _|].
    pose proof (@gmapO_leibniz (nat * loc) _ _ (leibnizO val) Hleib).
    apply H in Hi as -> =>//.
  Qed.

  Global Instance stack_location_cut_ne (n : nat) : (forall k, NonExpansive (stack_location_cut n k)).
  Proof.
    unfold stack_location_cut. intros k m v1 v2 Hm.
    rewrite /stack_cond /=. case_match.
    - apply bool_decide_eq_true in H.
      rewrite bool_decide_true //. f_equiv. auto.
    - apply bool_decide_eq_false in H.
      rewrite bool_decide_false //.
  Qed.

  Lemma stack_map_idemp (n : nat) (l : nat * loc) (v v' : leibnizO val) :
    stack_location_cut n l v = Some v' → stack_location_cut n l v' = Some v'.
  Proof.
    rewrite /stack_location_cut.
    case_match;[|naive_solver].
    intros Heq. simplify_eq.
    rewrite H //.
  Qed.    

  Global Instance stack_mapTrans (n : nat) : MapTrans (stack_location_cut n).
  Proof.
    split.
    - apply stack_map_trans_frag_discard_all.
    - apply stack_map_idemp.
    - apply stack_location_cut_ne.
  Qed.
    
  Inductive stack_cut_rel : nat -> gmap (nat * loc) val -> gmap (nat * loc) val -> Prop :=
  | stack_cut_rel_cond (n : nat) (σ : gmap (nat * loc) val) (σ' : gmap (nat * loc) val) :
    (forall m l v, σ !! (m,l) = Some v -> m < n -> σ' !! (m,l) = Some v) ->
    (forall m l v, σ !! (m,l) = Some v -> m >= n -> σ' !! (m,l) = None) ->
    stack_cut_rel n σ σ'.

  Lemma stack_cut_0 s : stack_cut 0 s = ∅.
  Proof.
    rewrite /stack_cut /stack_cond.
    rewrite map_filter_empty_iff. apply map_Forall_lookup.
    intros. simpl. lia.
  Qed.
  
  Lemma stack_cut_full s n : (forall l, l ∈ dom s -> l.1 < n) -> stack_cut n s = s.
  Proof.
    intros Hgt.
    rewrite /stack_cut /stack_cond. rewrite map_filter_id//.
    intros [m l] x Hx. apply elem_of_dom_2 in Hx. apply Hgt in Hx. auto.
  Qed.

  Lemma stack_cut_snoc s n m x l :
    n <= m ->
    stack_cut n (<[(m,l) := x]> s) = stack_cut n s.
  Proof.
    intros Hle.
    rewrite /stack_cut /stack_cond.
    rewrite map_filter_insert_not//.
    intros y. simpl. lia.
  Qed.

  Lemma stac_cut_snoc_gt s n m x l :
    n > m ->
    stack_cut n (<[(m,l) := x]> s) = <[(m,l) := x]> (stack_cut n s).
  Proof.
    intros Hgt. rewrite /stack_cut /stack_cond.
    rewrite map_filter_insert. simpl.
    rewrite decide_True//.
  Qed.

  Lemma popN_stack_lookup_Some s1 i n g :
    popN_stack s1 i !! n = Some g ->
    s1 !! n = Some g.
  Proof.
    revert s1 n g. induction i;intros s1 n g.
    - simpl. auto.
    - simpl. intros Hs.
      unfold pop_stack in Hs.
      destruct s1 using rev_ind;auto.
      clear IHs1. rewrite reverse_snoc reverse_involutive in Hs.
      apply IHi in Hs. rewrite lookup_app_l//.
      apply lookup_lt_Some in Hs =>//.
  Qed.

  Lemma popN_stack_length s i :
    length (popN_stack s i) = length s - i.
  Proof.
    revert s;induction i;intros s.
    - rewrite /=. lia.
    - simpl.  specialize (IHi (pop_stack s)).
      rewrite IHi. rewrite /pop_stack.
      destruct s using rev_ind;simpl;[lia|].
      rewrite reverse_snoc reverse_involutive.
      rewrite app_length /=. lia.
  Qed.      

  Lemma popN_stack_lookup_lt s1 i n g :
    popN_stack s1 i !! n = Some g ->
    n < length s1 - i.
  Proof.
    intros Hs. apply lookup_lt_Some in Hs.
    rewrite popN_stack_length in Hs. auto.
  Qed.

  Lemma popN_stack_lookup_None s1 i n :
    popN_stack s1 i !! n = None ->
    s1 !! n = None \/ n >= length s1 - i.
  Proof.
    revert s1 n. induction i;intros s1 n.
    - simpl. auto.
    - simpl. intros Hs.
      unfold pop_stack in Hs.
      destruct s1 using rev_ind;auto.
      clear IHs1. rewrite reverse_snoc reverse_involutive in Hs.
      apply IHi in Hs as [Hnone | Hge].
      + destruct (decide (n = length s1)).
        * subst. right. rewrite app_length /=.
          lia.
        * apply lookup_ge_None_1 in Hnone as Hge.
          assert (length s1 < n);[lia|].
          rewrite lookup_ge_None_2;auto.
          rewrite app_length /=. lia.
      + right. rewrite app_length /=. lia.
  Qed.

  Lemma stack_location_cut_popN_stack s1 i :
    map_imap (stack_location_cut (length s1 - i)) (list_to_gmap_stack s1) = list_to_gmap_stack (popN_stack s1 i).
  Proof.
    apply map_eq.
    intros [n l]. rewrite list_to_gmap_stack_lookup.
    rewrite map_lookup_imap list_to_gmap_stack_lookup.
    destruct (popN_stack s1 i !! n) eqn:Hsome1.
    - apply popN_stack_lookup_Some in Hsome1 as Hsome2.
      rewrite Hsome2 Hsome1 /= /stack_location_cut /=.
      destruct (g !! l) =>// /=.
      rewrite bool_decide_eq_true_2 //.
      rewrite /stack_cond /=.
      apply popN_stack_lookup_lt in Hsome1. auto.
    - apply popN_stack_lookup_None in Hsome1 as Hnone.
      destruct Hnone as [Hnone|Hge];[rewrite Hnone Hsome1 /= //|].
      rewrite Hsome1 /=. destruct (s1 !! n) eqn:Hnone;auto.
      simpl. destruct (g !! l) eqn:Hl;auto.
      simpl. rewrite /stack_location_cut bool_decide_eq_false_2//.
      rewrite /stack_cond /=. lia.
  Qed.
  
  
End pop_func.
