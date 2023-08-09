From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From iris.program_logic Require Export weakestpre.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting.
From nextgen.case_study Require Export stack_lang stack_transform.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From nextgen Require Import nextgen_basic gen_trans gmap_view_transformation nextgen_pointwise.
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

Instance gmap_view_inG `{heapGS Σ} : inG Σ (gmap_view.gmap_viewR (nat * loc) (leibnizO val)).
Proof. destruct H,heapG_gen_stackGS0,gen_heap_inG,gen_heapGpreS_heap =>//. Qed.

Definition state_trans (σ : state) := (map_entry_lift_gmap_view (stack_location_cut (length σ.2))).
Definition stack_gname `{heapGS Σ} := gen_heap_name heapG_gen_stackGS.

Lemma intro_id {PROP: bi} (P : PROP) : (P ⊢ P)%I. Proof. auto. Qed.

Instance heapG_irisGS `{heapGS Σ} : irisGS_gen _ lang Σ := {
    iris_invGS := heapG_invGS;
    next_state σ :=
      trans_single stack_gname (state_trans σ);
    state_interp σ _ _ _ :=
      let '(h,s) := σ in
      (gen_heap_interp h
         ∗ gen_heap_interp (list_to_gmap_stack s)
         ∗ own heapG_stacksize_name (excl_auth_auth (length s)))%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := intro_id _ (* fupd_intro _ _ *)
}.
Global Opaque iris_invGS.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.
Notation "i @@ l ↦{ q } v" := (mapsto (L:=nat * loc) (V:=val) (i,l) q v%V)
  (at level 20, l at next level, q at next level, format "i  @@  l  ↦{ q }  v") : bi_scope.
Notation "i @@ l ↦ v" :=
  (mapsto (L:=nat*loc) (V:=val) (i,l) (DfracOwn 1) v%V) (at level 20, l at next level, v at next level) : bi_scope.
Notation "i @@ l ↦{ q } -" := (∃ v, i @@ l ↦{q} v)%I
  (at level 20, l at next level, q at next level, format "i  @@  l  ↦{ q }  -") : bi_scope.
(* Notation "i @@ l ↦ -" := (i @@ l ↦{DfracOwn 1} -)%I (at level 20) : bi_scope. *)
Notation "[size] n" := (own heapG_stacksize_name (excl_auth_frag n)) (at level 20, format "[size]  n") : bi_scope.

Section heapG_nextgen_updates.
  Context `{heapGS Σ}.
  
  Lemma stacksize_own_agree_ng n σ ns κs nt :
    [size] n -∗ (⚡={next_state σ}=> |==> state_interp σ ns κs nt) -∗ ⌜n = (length σ.2)⌝.
  Proof.
    iIntros "Hs Hσ".
    iDestruct (trans_single_own_other stack_gname (state_trans σ) with "Hs") as "Hs".
    { admit. (* will have to be changed to either compare indices, or gnames *) }
    iApply (bnextgen_plain (trans_single stack_gname (state_trans σ))).
    iModIntro. destruct σ as [h' s'].
    simpl. iApply bupd_plain. iDestruct "Hσ" as ">(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$Hsize $Hs]") as %Hs.
    auto.
  Admitted.


  Lemma gen_heap_alloc_stack_ng σ ns κs nt l v :
    is_Some (σ.2 !! 0) ->
    (list_to_gmap_stack σ.2) !! ((length σ.2 - 1),l) = None ->
    (⚡={next_state σ}=> |==> state_interp σ ns κs nt) -∗
    ⚡={next_state σ}=> |==> state_interp (<[ (length σ.2 - 1) @ l := v ]> σ) ns κs nt ∗ ((length σ.2 - 1) @@ l ↦ v).
  Proof.
    iIntros ([s0 Hs0] Hnone) "Hstate".
    iModIntro. 
    destruct σ as [h1 s1]. simpl in *.
    iDestruct "Hstate" as ">(Hh & Hstk & Hsize) /=".
    iDestruct (gen_heap_alloc _ _ v with "Hstk") as ">[Hstk [Hl _]]";[eauto|].
    rewrite /insert /= PeanoNat.Nat.sub_diag Hs0.
    assert (map_insert (length s1 - 1, l) v (list_to_gmap_stack s1) = list_to_gmap_stack (<[0:=<[l:=v]> s0]> s1)) as ->;[admit|].
    iFrame. iModIntro.
    rewrite insert_length. iFrame.
  Admitted.

  
End heapG_nextgen_updates.

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
  
  (* SallocS K e v σ l : *)
  (*   to_val e = Some v -> *)
  (*   scope v 0 -> *)
  (*   [[σ @ 0]] !! l = None -> *)
  (*   head_step K (Salloc e) σ [] (Loc (local 0) l) (<[0@l:=v]>σ) [] NormalMode *)

  Lemma wp_stack_alloc K E n e v Φ `{!IntoVal e v} :
    0 < n -> (* stack is non empty *)
    scope v 0 ->
    ▷ (∀ l, [size] n -∗ WP fill K (Loc (local 0) l) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (Salloc e) @ E {{ Φ }}.
  Proof.
    iIntros (Hlt scope) "[HΦ >Hsize]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "Hstate".
    iDestruct (stacksize_own_agree_ng with "Hsize Hstate") as %Hsize. simpl in Hsize.
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    assert (is_Some (s1 !! (length s1 - 1))) as [s' Hs'].
    { apply lookup_lt_is_Some. lia. }
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. apply salloc_fresh;eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls".
    rewrite /insert /= PeanoNat.Nat.sub_0_r Hs' /state_trans insert_length /=.
    rewrite -/(state_trans (h1,s1)).
    iDestruct (gen_heap_alloc_stack_ng _ ns κs nt l v0 with "Hstate") as "Hstate".
    { apply lookup_lt_is_Some. auto. }
    { simpl. rewrite /lookup_stack /= in H4. admit. }
    
    Abort.
    
    (* simpl. simpl. simpl. unfold lookup_stack in H4. *)
    (* simpl in H4. rewrite H4. insert_state. *)
    
    
    
    (* iAssert (⚡={next_state (h1, s1)}=> _ ∗ _ ∗ _)%I with "[Hstate]" as "Hl". *)
    (* { iModIntro. iDestruct "Hstate" as "(Hh & Hstk & Hsize) /=". *)
    (*   iSplitR "Hh Hsize";[|iSplitL "Hh";[iExact "Hh"|iExact "Hsize"] ]. *)
    (*   iApply (gen_heap_alloc with "Hstk"). admit. } *)
    
    

  (** Control flow -- stateful due to stack frames *)
  (* Lemma wp_call_global K E n k x e1 e2 v2' v2 Φ `{!IntoVal e2 v2} : *)
  (*   shift_val v2 (-1) = v2' -> *)
  (*   ▷ ([size] (S n) -∗ WP fill K (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1))) @ E {{ Φ }}) *)
  (*     ∗ ▷ [size] n *)
  (*     ⊢ WP fill K (Call (Lam global k x e1) e2) @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hshift) "[HΦ >Hs]". *)
  (*   iApply wp_lift_nonthrow_head_step; auto. *)
  (*   iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=". *)
  (*   iDestruct (stacksize_own_agree with "[$]") as %Heq;subst. *)
  (*   iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]". *)
  (*   iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls". *)
  (*   iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. } *)
  (*   iNext. iIntros (rm r0 σ2 efs Hstep) "Hp". *)
  (*   inv_head_step. iMod "Hcls". iModIntro. *)
  (*   rewrite list_to_gmap_stack_push_stack push_stack_length. *)
  (*   iFrame. iApply "HΦ". iFrame. *)
  (* Qed. *)

  (* Lemma wp_call_local K E n i k x e1 e2 e1' v2' v2 Φ `{!IntoVal e2 v2} : *)
  (*   scope_tag (local i) -> *)
  (*   shift_expr e1 (i - 1) = e1' -> *)
  (*   shift_val v2 (-1) = v2' -> *)
  (*   ▷ ([size] (S n) -∗ WP fill K (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1'))) @ E {{ Φ }}) *)
  (*     ∗ ▷ [size] n *)
  (*     ⊢ WP fill K (Call (Lam (local i) k x e1) e2) @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hscope Hshift1 Hshift2) "[HΦ >Hs]". *)
  (*   iApply wp_lift_nonthrow_head_step; auto. *)
  (*   iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=". *)
  (*   iDestruct (stacksize_own_agree with "[$]") as %Heq;subst. *)
  (*   iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]". *)
  (*   iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls". *)
  (*   iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. } *)
  (*   iNext. iIntros (rm r0 σ2 efs Hstep) "Hp". *)
  (*   inv_head_step. iMod "Hcls". iModIntro. *)
  (*   rewrite list_to_gmap_stack_push_stack push_stack_length. *)
  (*   iFrame. iApply "HΦ". iFrame. *)
  (* Qed. *)

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
    (* iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=". *)
    (* iDestruct (stacksize_own_agree with "[$]") as %Heq;subst. *)
    (* iMod (stacksize_own_update (length s1 - Z.abs_nat i) with "[$]") as "[Hsize Hs]". *)
    (* iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls". *)
    (* iSplit. { iPureIntro. repeat econstructor; eauto. } *)
    (* iNext. iIntros (r0 σ2 efs Hstep) "Hp". *)
    (* inv_head_step. iMod "Hcls". iModIntro. iFrame. *)
  Abort.
(** TODO: change the state interpretation such that there is no need to deallocate points to's:
 two possibilities:
 (1) change the opsem so maintain a "top of frame" number and never remove parts of the state
 (2) allow a larger gen_heap. This becomes quite tricky when pushing though, since there will be clashing
 (3) generations? I need the non frame preserving update modality!!!
 (4) always have all fragments of the stack in the state interpretation *)


End lifting.
