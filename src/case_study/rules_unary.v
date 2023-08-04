From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From iris.program_logic Require Export weakestpre.
From self.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting.
From self.case_study Require Export stack_lang gmap_transformation.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From self Require Import nextgen_basic gen_trans.
Set Default Proof Using "Type".
Import uPred.

(** Basic rules for language operations. *)

(* CMRA for size *)
Class stacksizeGS Σ := StackSizeGS {
  heapG_stacksize_name : gname;
  heapG_excl_nat_stacksizeGS :> inG Σ (excl_authUR natR)
}.
(* CMRA for state interpretation *)
Class heapGS Σ := HeapGS {
  heapG_invGS : invGS Σ;
  heapG_gen_heapGS :> gen_heapGS loc val Σ;
  heapG_gen_stackGS :> gen_heapGS (nat * loc) val Σ;
  heapG_stacksizeGS :> stacksizeGS Σ
}.

Section StackSize.
  Context `{!heapGS Σ}.

  Lemma stacksizeRA_valid_full (m n : natR) : ✓ (●E m ⋅ ◯E n) → n = m.
  Proof.
    by intros ?%excl_auth_agree.
  Qed.

  Lemma stacksizeRA_update (m n m': natR) : (●E m ⋅ ◯E n) ~~> (●E m') ⋅ (◯E m').
  Proof.
    apply excl_auth_update.
  Qed.

  Lemma stacksize_own_agree (m n : nat) :
    own heapG_stacksize_name (excl_auth_auth m) ∗ own heapG_stacksize_name (excl_auth_frag n) -∗ ⌜n = m⌝.
  Proof.
    iIntros "[Hm Hn]".
    iDestruct (own_valid_2 with "Hm Hn") as %Hv%stacksizeRA_valid_full;auto.
  Qed.

  Lemma stacksize_own_update (m' m n : nat) :
    own heapG_stacksize_name (excl_auth_auth m) ∗ own heapG_stacksize_name (excl_auth_frag n) ==∗
    own heapG_stacksize_name (excl_auth_auth m') ∗ own heapG_stacksize_name (excl_auth_frag m').
  Proof.
    iIntros "[Hm Hn]".
    pose proof (stacksizeRA_update m n m') as Hupd.
    iMod (own_update_2 with "Hm Hn") as "[$ $]";eauto.
  Qed.
    
End StackSize.

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

Instance heapG_irisGS `{heapGS Σ} : irisGS lang Σ := {
    iris_invGS := heapG_invGS;
    state_interp σ _ _ _ :=
      let '(h,s) := σ in
      (gen_heap_interp h
         ∗ gen_heap_interp (list_to_gmap_stack s)
         ∗ own heapG_stacksize_name (excl_auth_auth (length s)))%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.
Global Opaque iris_invGS.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.
Notation "i @@ l ↦{ q } v" := (mapsto (L:=nat * loc) (V:=val) (i,l) q v%V)
  (at level 20, l at next level, q at next level, format "i  @@  l  ↦{ q }  v") : bi_scope.
Notation "i @@ l ↦ v" :=
  (mapsto (L:=nat*loc) (V:=val) (i,l) 1 v%V) (at level 20, l at next level) : bi_scope.
Notation "i @@ l ↦{ q } -" := (∃ v, i @@ l ↦{q} v)%I
  (at level 20, l at next level, q at next level, format "i  @@  l  ↦{ q }  -") : bi_scope.
Notation "i @@ l ↦ -" := (i @@ l ↦{1} -)%I (at level 20) : bi_scope.
Notation "[size] n" := (own heapG_stacksize_name (excl_auth_frag n)) (at level 20, format "[size]  n") : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : IntoVal _ _ |- _ => rewrite /IntoVal /= in H
  | H : AsVal _ |- _ => destruct H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : of_val _ = Some _ |- _ => progress rewrite (of_to_val _ _ H)
  | H : to_val ?v _ = _ |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step _ ?e _ _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _, _, _; simpl : core.

Local Hint Constructors head_step : core.
Local Hint Resolve halloc_fresh : core.
Local Hint Resolve salloc_fresh : core.
Local Hint Resolve to_of_val : core.

Section pop_func.
  (* Context `{heapGS Σ}. *)

  Definition stack_cut (n : nat) (s : stack) : stack := popN_stack s (length s - n).
  Inductive stack_cut_rel : nat -> gmap (nat * loc) val -> gmap (nat * loc) val -> Prop :=
  | stack_cut_rel_cond (n : nat) (σ : gmap (nat * loc) val) (σ' : gmap (nat * loc) val) :
    (forall m l v, σ !! (m,l) = Some v -> m < n -> σ' !! (m,l) = Some v) ->
    (forall m l v, σ !! (m,l) = Some v -> m >= n -> σ' !! (m,l) = None) ->
    stack_cut_rel n σ σ'.

  Lemma stack_cut_0 s : stack_cut 0 s = [].
  Proof. rewrite /stack_cut PeanoNat.Nat.sub_0_r. apply popN_stack_empty. Qed.
  
  Lemma stack_cut_full s n : n >= length s -> stack_cut n s = s.
  Proof.
    intros Hgt.
    rewrite /stack_cut. assert (length s - n = 0) as ->;[lia|auto].
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

  Lemma stack_cut_snoc s n x :
    n <= length s ->
    stack_cut n (s ++ [x]) = stack_cut n s.
  Proof.
    intros Hle.
    rewrite /stack_cut /= app_length.
    assert (length s + length [x] - n = (length s - n) + length [x]) as ->; [lia|].
    rewrite popN_stack_spec;auto.
  Qed.

  Lemma stac_cut_snoc_gt s n x :
    n > length s ->
    stack_cut n (s ++ [x]) = s ++ [x].
  Proof.
    intros Hgt.
    apply stack_cut_full. rewrite app_length /=. lia.
  Qed.

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

  (* Lemma list_to_gmap_stack_lookup s m l : *)
  (*   is_Some (list_to_gmap_stack s !! (m, l)) -> *)

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

  Lemma list_to_gmap_lookup_stack_cut n s m l :
    m < n ->
    (list_to_gmap_stack (stack_cut n s)) !! (m, l) = (list_to_gmap_stack s) !! (m, l).
  Proof.
    intros Hlt.
    destruct (list_to_gmap_stack s !! (m, l)) eqn:Hsome.
    - apply list_to_gmap_stack_lookup_Some in Hsome as Hlt'.
      rewrite /list_to_gmap_stack lookup_gmap_uncurry.
      rewrite /list_to_gmap_stack lookup_gmap_uncurry in Hsome.
  Admitted.

  Lemma stack_cut_list_to_gmap_stack (s : stack) (n : nat) :
    stack_cut_rel n (list_to_gmap_stack s) (list_to_gmap_stack (stack_cut n s)).
  Proof.
    revert n; induction s using rev_ind;intros n.
    - unfold list_to_gmap_stack.
      constructor;auto.
    - (* unfold list_to_gmap_stack. *)
      (* rewrite list_to_gmap_stack_fix_snoc. *)
      (* rewrite stack_cut_snoc. *)
      constructor.
      + intros m l v Hsome Hlt.
        apply list_to_gmap_stack_lookup_Some in Hsome as Hlt'.
        (* unfold list_to_gmap_stack. *)
        rewrite app_length /= in Hlt'.
        destruct (decide (n <= length s)).
        * rewrite stack_cut_snoc//.
          assert (m < length s);[lia|].
          rewrite list_to_gmap_lookup_snoc// in Hsome.
  Admitted.
          

  (* The functor in [Σ] at index [i] applied to [iProp]. *)
  Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).
  (* The functor in [Σ] at index [i] applied to [iPreProp]. *)
  Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).

  Local Definition map_unfold {Σ} {i : gid Σ} : R Σ i -n> Rpre Σ i :=
    rFunctor_map _ (iProp_fold, iProp_unfold).
  Local Definition map_fold {Σ} {i : gid Σ} : Rpre Σ i -n> R Σ i :=
    rFunctor_map _ (iProp_unfold, iProp_fold).

  Definition stackM : cmra := gmap_view.gmap_viewUR (nat * loc) (leibnizO val).

  (* Definition fG_resp_stack_cut {Σ : gFunctors} {heapG: heapGS Σ} : iProp Σ := *)
  (*   ∀ (m : iResUR Σ) i γ, m i !!  *)

(*   Program Definition stack_cut_trans (σ: stackM) : stackM. *)
(*   Proof. *)
(*     destruct σ. *)
(*     destruct view_auth_proj. *)
(*     - destruct p. destruct a. *)
(*       repeat split. left. split;auto. *)
      

(*   Definition fG_resp_stack_cut {Σ : gFunctors} {heapG: heapGS Σ} : iProp Σ := *)
(*     ∀ (m : iResUR Σ) i γ a *)
  
(*   Program Definition nextgen_stack_cut {Σ : gFunctors} {heapG: heapGS Σ} P : iProp Σ := *)
(*     ∀ (fG: iResUR Σ → iResUR Σ) (_ : GenTrans fG), *)
(*       (∀ (m: iResUR Σ) i γ, ⌜(fG m) i !! γ = Some _⌝) → *)
(*       ⚡={fG}=> P. *)


(*   (* The functor [fG] respects the conditions in [Ω] and the entries in *)
(* [picks]. *) *)
(* Definition fG_resp {Σ} (fG : iResUR Σ → iResUR Σ) (Ω : gTransforms) (picks : Picks Σ) := *)
(*   ∀ (m : iResUR Σ) i γ a gti, *)
(*     m i !! γ = Some a → (* For every element in the old element. *) *)
(*     Ω.(g_valid_gt) i = Some2 gti → (* Where we have transformation conditions. *) *)
(*     ∃ t, (* There exists a transformation. *) *)
(*       Proper ((≡) ==> (≡)) t ∧ *)
(*       (fG m) i !! γ = Some (map_unfold (t (map_fold a))) ∧ *)
(*       gti.(gti_valid).(gt_condition) t ∧ *)
(*       (∀ t', picks i !! γ = Some t' → t = t'). *)

(* Definition m_contains_tokens_for_picks {Σ} Ω (picks : Picks Σ) (m : iResUR Σ) := *)
(*   ∀ i, *)
(*     dom (picks i) ≡ dom (m i) ∧ *)
(*     (∀ (γ : gname) (a : Rpre Σ i), *)
(*       m i !! γ = Some a  → *)
(*       ∃ gti (t : gti.(gti_car) → gti.(gti_car)), *)
(*         Ω.(g_valid_gt) i = Some2 gti ∧ *)
(*         picks i !! γ = Some (cmra_map_transport gti.(gti_look) (gen_generation t)) ∧ *)
(*         a ≡ map_unfold (cmra_transport (gti.(gti_look)) (None, GTS_tok_gen_shot t, None))). *)

(* Definition nextgen {Σ : gFunctors} {Ω : gTransforms} P : iProp Σ := *)
(*   ∃ (picks : Picks Σ) (m : iResUR Σ), *)
(*     ⌜ picks_valid Ω picks ⌝ ∗ *)
(*     uPred_ownM m ∗ ⌜ m_contains_tokens_for_picks Ω picks m ⌝ ∗ *)
(*     ∀ (fG : iResUR Σ → _) (_ : GenTrans fG) (_ : fG_resp fG Ω picks ), *)
(*       ⚡={fG}=> P. *)

(*   Program Definition cut_stack (s : stackM) : stackM. *)
(*   Proof. destruct s. *)
(*          destruct view_auth_proj. *)

(*          destruct σ. destruct gen_heap_inG. *)
(*          destruct gen_heapGpreS_heap. *)

(*          split. unfold gen_heapGpreS in gen_heap_inG. *)
  
  
End pop_func.

Section lifting.
  Context `{heapGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types κ κs : list observation.
  Implicit Types efs : list expr.
  Implicit Types σ : state.

  Hint Extern 1 =>
         match goal with
         | |- ∀ σ, head_nonthrow_reducible _ _ σ => repeat econstructor
         end : core.

  Hint Extern 1 =>
         match goal with
         | _ : head_step _ _ _ _ _ _ _ _ |- _ => inv_head_step
         end : core.

  Hint Extern 1 =>
         match goal with
         | H : IntoVal ?e ?v |- to_val ?e = Some _ => rewrite <- H; eauto
         | H : language.of_val ?v = ?e |- to_val ?e = Some _ => rewrite <- H; eauto
         end : core.
  
  (** Base axioms for core primitives of the language: Stateless reductions *)

  Lemma wp_LetIn K E e1 e2 v1 x Φ `{!IntoVal e1 v1} :
                               ▷ WP fill K (subst' x v1 e2) @ E {{ Φ }} ⊢ WP fill K (LetIn x e1 e2) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_nonthrow_pure_det_head_step_no_fork' K (LetIn _ _ _)) /=; eauto.
  Qed.

  Lemma wp_bin_op K E op e1 e2 v1 v2 w Φ `{!IntoVal e1 v1, !IntoVal e2 v2} :
    binop_eval op v1 v2 = Some w →
    ▷ WP fill K (of_val w) @ E {{ Φ }}
      ⊢ WP fill K (BinOp op e1 e2) @ E {{ Φ }}.
  Proof.
    intros ?.
    rewrite -(wp_lift_nonthrow_pure_det_head_step_no_fork' K (BinOp op _ _)) /=;eauto.
  Qed.

  Lemma wp_if_true K E e1 e2 Φ :
    ▷ WP fill K e1 @ E {{ Φ }} ⊢ WP fill K (If (#♭ true) e1 e2) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_nonthrow_pure_det_head_step_no_fork' K (If _ _ _)) /=;
               eauto.
  Qed.

  Lemma wp_if_false K E e1 e2 Φ :
    ▷ WP fill K e2 @ E {{ Φ }} ⊢ WP fill K (If (#♭ false) e1 e2) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_nonthrow_pure_det_head_step_no_fork' K (If _ _ _)) /=;
               eauto.
  Qed.

  Lemma wp_fst K E e1 e2 v1 Φ `{!IntoVal e1 v1, !AsVal e2} :
    ▷ WP fill K e1 @ E {{ Φ }}
      ⊢ WP fill K (Fst (Pair e1 e2)) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_nonthrow_pure_det_head_step_no_fork' K (Fst _)) /=;
               inv_head_step; eauto.
  Qed.

  Lemma wp_snd K E e1 e2 v2 Φ `{!AsVal e1, !IntoVal e2 v2} :
    ▷ WP fill K e2 @ E {{ Φ }}
      ⊢ WP fill K (Snd (Pair e1 e2)) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_nonthrow_pure_det_head_step_no_fork' K (Snd _)) /=;
               inv_head_step; eauto.
  Qed.

  (** Control flow -- stateful due to stack frames *)
    
  Lemma wp_call_global K E n k x e1 e2 v2' v2 Φ `{!IntoVal e2 v2} :
    shift_val v2 (-1) = v2' ->
    ▷ ([size] (S n) -∗ WP fill K (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1))) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (Call (Lam global k x e1) e2) @ E {{ Φ }}.
  Proof.
    iIntros (Hshift) "[HΦ >Hs]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$]") as %Heq;subst.
    iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls". iModIntro.
    rewrite list_to_gmap_stack_push_stack push_stack_length.
    iFrame. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_call_local K E n i k x e1 e2 e1' v2' v2 Φ `{!IntoVal e2 v2} :
    scope_tag (local i) ->
    shift_expr e1 (i - 1) = e1' ->
    shift_val v2 (-1) = v2' ->
    ▷ ([size] (S n) -∗ WP fill K (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1'))) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (Call (Lam (local i) k x e1) e2) @ E {{ Φ }}.
  Proof.
    iIntros (Hscope Hshift1 Hshift2) "[HΦ >Hs]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$]") as %Heq;subst.
    iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls". iModIntro.
    rewrite list_to_gmap_stack_push_stack push_stack_length.
    iFrame. iApply "HΦ". iFrame.
  Qed.

(*| ReturnS K K' i e e' v σ :
    to_val e = Some v ->
    shift_expr e i = e' ->
    (i <= 0)%Z ->
    length (stack_of σ) >= Z.abs_nat i ->
    head_step K (Return (Cont i K') e) σ [] (foldl (flip fill_item) e' K') (popN σ (Z.abs_nat i)) [] ThrowMode *)
  
  Lemma wp_return K K' E n i e e' v Φ `{!IntoVal e v} :
    (i <= 0)%Z ->
    Z.abs_nat i <= n ->
    shift_expr e i = e' ->
    ▷ ([size] (n - (Z.abs_nat i)) -∗ WP fill K' e @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (Return (Cont i K') e) @ E {{ Φ }}.
  Proof.
    iIntros (Hle Hlen Hshift) "[HΦ >Hn]".
    iApply wp_lift_throw_head_step;auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$]") as %Heq;subst.
    iMod (stacksize_own_update (length s1 - Z.abs_nat i) with "[$]") as "[Hsize Hs]".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit. { iPureIntro. repeat econstructor; eauto. }
    iNext. iIntros (r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls". iModIntro. iFrame.
  Abort.
(** TODO: change the state interpretation such that there is no need to deallocate points to's:
 two possibilities:
 (1) change the opsem so maintain a "top of frame" number and never remove parts of the state
 (2) allow a larger gen_heap. This becomes quite tricky when pushing though, since there will be clashing
 (3) generations? I need the non frame preserving update modality!!!
 (4) always have all fragments of the stack in the state interpretation *)


End lifting.
