From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting weakestpre.
From nextgen.case_study Require Export stack_lang stack_transform.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From nextgen Require Import nextgen_basic gen_trans gmap_view_transformation nextgen_pointwise nextgen_id.
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

Instance gmap_view_inG `{H:heapGS Σ} : inG Σ (gmap_view.gmap_viewR (nat * loc) (leibnizO val)) :=
  (((H.(heapG_gen_stackGS)).(gen_heap_inG)).(gen_heapGpreS_heap)).(ghost_map.ghost_map_inG _ _ _ _ _).

Definition state_trans (n : nat) := (map_entry_lift_gmap_view (stack_location_cut n)).
Definition state_trans_state (σ : state) := state_trans (length σ.2).
Definition stack_gname `{heapGS Σ} := gen_heap_name heapG_gen_stackGS.

Program Definition next_state_f `{heapGS Σ} (e : stack_expr) : iResUR Σ → iResUR Σ :=
  match find_i e.2 with
  | Some i => trans_single stack_gname (state_trans (e.1 - (Z.abs_nat i)))
  | None => id
  end.

#[global]
Instance next_state_f_cmra_morphism : ∀ (Σ : gFunctors) (H : heapGS Σ) (e : language.expr lang), CmraMorphism (next_state_f e).
Proof.
  intros.
  unfold next_state_f. destruct (find_i e.2);apply _.
Qed.

Lemma intro_id {PROP: bi} (P : PROP) : (P ⊢ P)%I. Proof. auto. Qed.

Definition gen_stack_interp `{H : heapGS Σ} s :=
  @ghost_map.ghost_map_auth Σ _ _ _ _
    ((H.(heapG_gen_stackGS)).(gen_heap_inG)).(gen_heapGpreS_heap) (gen_heap_name heapG_gen_stackGS) 1 (list_to_gmap_stack s).

Program Instance heapG_irisGS `{heapGS Σ} : irisGS_gen _ lang Σ := {
    iris_invGS := heapG_invGS;
    state_interp σ _ _ _ :=
      let '(h,s) := σ in
      (gen_heap_interp h
         ∗ (* gen_heap_interp (list_to_gmap_stack s) *) gen_stack_interp s
         ∗ own heapG_stacksize_name (excl_auth_auth (length s)))%I;
    next_state := next_state_f;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := intro_id _ (* fupd_intro _ _ *)
  }.
Global Opaque iris_invGS.

#[global]
Instance heapG_next_monotone `{heapGS Σ} : NextMonotone.
Proof.
  constructor. intros. simpl in *.
  unfold CC_ectxi_language.fill.
  destruct e1;simpl in *. rewrite /stack_to_val in H0.
  simpl in H0.
  destruct (to_val e) eqn:He;try done.
  unfold next_state_f. rewrite fill_proj /=.
  destruct (find_i e) eqn:Hfind.
  - eapply find_i_fill in Hfind as ->.
    rewrite fill_proj_fst_eq. simpl. auto.
  - destruct (find_i (foldl (flip fill_item) e K)) eqn:Hcontr;auto.
    eapply fill_find_i in Hcontr;auto. congruence.
Qed.    

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{DfracOwn 1} -)%I (at level 20) : bi_scope.

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
    [size] n -∗ state_interp σ ns κs nt -∗ ⌜n = (length σ.2)⌝.
  Proof.
    iIntros "Hs Hσ". destruct σ as [h' s'].
    simpl. iDestruct "Hσ" as "(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$Hsize $Hs]") as %Hs;auto.
  Qed.

  Lemma gen_heap_alloc_stack_ng σ ns κs nt l v :
    is_Some (σ.2 !! (length σ.2 - 1)) ->
    (list_to_gmap_stack σ.2) !! ((length σ.2 - 1),l) = None ->
    state_interp σ ns κs nt ==∗
    state_interp (<[ 0 @ l := v ]> σ) ns κs nt ∗ (length σ.2 - 1) @@ l ↦ v.
  Proof.
    iIntros ([s0 Hs0] Hnone) "Hstate".
    destruct σ as [h1 s1]. simpl snd in *.
    iDestruct "Hstate" as "(Hh & Hstk & Hsize)".
    iDestruct (ghost_map.ghost_map_insert _ v with "Hstk") as ">[Hstk Hl]";[eauto|].
    rewrite /mapsto seal_eq /gen_heap.mapsto_def.
    rewrite (list_to_gmap_stack_insert _ s0)//.
    simpl. rewrite /insert /insert_state_Insert /=.
    rewrite PeanoNat.Nat.sub_0_r Hs0 insert_length. iFrame.
    done.
  Qed.

  Lemma gen_stack_valid (s : stack) (h : heap) (j : nat) (l : loc) (w : val) :
    (length s - 1 - j) @@ l ↦ w -∗ gen_stack_interp s -∗ ⌜[[ (h,s) @ j ]] !! l = Some w ⌝.
  Proof.
    iIntros "Hl Hs".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def.
    iDestruct (ghost_map.ghost_map_lookup with "Hs Hl") as %Hlookup.
    rewrite list_to_gmap_stack_lookup in Hlookup.
    rewrite /lookup /lookup_state_Lookup /lookup_state /lookup_stack /=.
    auto.
  Qed.

  Lemma gen_stack_update s s0 j l w w' :
    s !! (length s - 1 - j) = Some s0 ->
    (length s - 1 - j) @@ l ↦ w -∗ gen_stack_interp s ==∗ (length s - 1 - j) @@ l ↦ w' ∗ gen_stack_interp (<[length s - 1 - j:=<[l:=w']> s0]> s).
  Proof.
    iIntros (Hs0) "Hl Hs".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def.
    iMod (ghost_map.ghost_map_update with "Hs Hl") as "[Hs Hl]". iFrame.
    erewrite list_to_gmap_stack_insert =>//.
  Qed.

  Lemma gen_stack_interp_stack_pop s1 i :
    length s1 ≥ i ->
    gen_stack_interp s1 -∗
    ⚡={trans_single stack_gname (state_trans ((length s1) - i))}=> gen_stack_interp (popN_stack s1 i).
  Proof.
    iIntros (Hl) "Hs".
    unfold gen_stack_interp. rewrite -/stack_gname.
    rewrite /ghost_map.ghost_map_auth seal_eq /ghost_map.ghost_map_auth_def.
    iDestruct (trans_single_own _ (state_trans (length s1 - i)) with "Hs") as "Hs".
    iModIntro. rewrite /state_trans /map_entry_lift_gmap_view /= /cmra_morphism_extra.fmap_view /= /cmra_morphism_extra.fmap_pair /=.
    rewrite /gMapTrans_frag_lift map_imap_empty /=.
    rewrite /gmap_view.gmap_view_auth /view_auth.
    rewrite agree_map_to_agree.
    rewrite stack_location_cut_popN_stack. iFrame.
  Qed.

  Lemma gen_heap_interp_stack_pop (h : heap) n :
    gen_heap_interp h -∗
    ⚡={trans_single stack_gname (state_trans n)}=> gen_heap_interp h.
  Proof.
    iIntros "Hh".
    rewrite /gen_heap_interp.
    iApply bnextgen_exist. iDestruct "Hh" as (m Hdom) "[Hh Hm]".
    iExists m. iApply bnextgen_sep_2. iSplitR.
    { iModIntro; auto. }
    iApply bnextgen_sep_2. iSplitR "Hm".
    - rewrite /ghost_map.ghost_map_auth seal_eq /ghost_map.ghost_map_auth_def.
      iApply trans_single_own_other;[admit|]. (* will go through with the new inG def *)
      iFrame.
    - rewrite /ghost_map.ghost_map_auth seal_eq /ghost_map.ghost_map_auth_def.
      iApply trans_single_own_other;[admit|]. (* will go through with the new inG def *)
      iFrame.
  Admitted.

  Lemma stack_size_auth_stack_pop s n :
    own heapG_stacksize_name (excl_auth_auth s) -∗
    ⚡={trans_single stack_gname (state_trans n)}=> own heapG_stacksize_name (excl_auth_auth s).
  Proof.
    iIntros "Hs".
    iApply trans_single_own_other;[admit|]. (* will go through with the new inG def *)
    iFrame.
  Admitted.

  Lemma heap_stack_pop_intro l q v n :
    l ↦{q} v -∗ ⚡={trans_single stack_gname (state_trans n)}=> l ↦{q} v.
  Proof.
    iIntros "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def.
    iApply trans_single_own_other;[admit|]. (* will go through with the new inG def *)
    iFrame.
  Admitted.

  Lemma stack_size_frag_stack_pop s n :
    [size] s -∗ ⚡={trans_single stack_gname (state_trans n)}=> [size] s.
  Proof.
    iIntros "Hs".
    iApply trans_single_own_other;[admit|]. (* will go through with the new inG def *)
  Admitted.

  Lemma stack_stack_pop_intro i l q v n :
    i < n ->
    i @@ l ↦{q} v -∗ ⚡={trans_single stack_gname (state_trans n)}=> i @@ l ↦{q} v.
  Proof.
    iIntros (Hle) "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def.
    rewrite -/stack_gname.
    iDestruct (trans_single_own _ (state_trans n) with "Hl") as "Hl".
    iModIntro.
    rewrite /state_trans /map_entry_lift_gmap_view /gmap_view.gmap_view_frag /=.
    rewrite /cmra_morphism_extra.fmap_view /=.
    rewrite /gMapTrans_frag_lift /=.
    rewrite map_imap_insert /= agree_option_map_to_agree /=.
    rewrite /stack_location_cut bool_decide_true // /=.
  Qed.
    
    
End heapG_nextgen_updates.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : IntoVal _ _ |- _ => rewrite /IntoVal /= in H; inversion H
    | H : AsVal _ |- _ => destruct H as [? HH];simpl in HH;inversion HH
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

(** Helper lemma to compute context *)
Lemma construct_ctx_eq (n : nat) (e : expr) :
  let '(Ks,e') := construct_ctx e in (n,e) = fill Ks (n,e').
Proof.
  destruct (construct_ctx e) eqn:Hctx.
  apply construct_ctx_fill in Hctx. subst e.
  rewrite /fill /= /CC_ectxi_language.fill.
  rewrite fill_proj_eq /= //.
Qed.

Section lifting.
  Context `{heapGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : stack_val → iProp Σ.
  Implicit Types κ κs : list observation.
  Implicit Types efs : list expr.
  Implicit Types σ : state.
  Implicit Types e : expr.

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
         | H : IntoVal (_,?e) ?v |- to_val ?e = Some _ => inversion H; eauto
         | H : language.of_val (_,?v) = ?e |- to_val ?e = Some _ => inversion H; eauto
         end : core.

  (** ------------------------------------------------------------ *)
  (** ------------------- Stateless reductions ------------------- *)
  (** ------------------------------------------------------------ *)

  Lemma next_state_letin_id n x e1 v1 e2 `{!IntoVal (n,e1) v1} :
    next_state_f (n, LetIn x e1 e2) = id.
  Proof.
    inv_head_step.
    rewrite /next_state_f /find_i /=.
    by erewrite construct_ctx_to_val;[|apply to_of_val].
  Qed.

  Ltac resolve_next_state :=
         match goal with
         | |- ∀ x, next_state_f _ _ = _ _ =>
             inv_head_step; rewrite /next_state_f /find_i /=; (try rewrite !to_of_val); (try rewrite construct_ctx_of_val /=); (try rewrite !to_of_val); simpl; auto
         | |- ∀ x, next_state _ _ = _ _ =>
             inv_head_step; rewrite /next_state /next_state_f /find_i /=; (try rewrite !to_of_val); (try rewrite construct_ctx_of_val /=); (try rewrite !to_of_val); simpl; auto
         end.

  Lemma wp_LetIn K E e1 e2 v1 x Φ (n : nat) `{!IntoVal (n,e1) v1} :
                               ▷ WP fill K (n,subst' x v1.2 e2) @ E {{ Φ }} ⊢ WP fill K (n,LetIn x e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,LetIn _ _ _) _);eauto.
    intros; inv_head_step;eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  Lemma wp_bin_op K E op e1 e2 n v1 v2 w Φ `{!IntoVal (n,e1) (n,v1), !IntoVal (n,e2) (n,v2)} :
    binop_eval op v1 v2 = Some w →
    ▷ WP fill K (n, of_val w) @ E {{ Φ }}
      ⊢ WP fill K (n, BinOp op e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,BinOp op _ _) _);eauto.
    intros; inv_head_step;eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  Lemma wp_if_true K E e1 e2 n Φ :
    ▷ WP fill K (n,e1) @ E {{ Φ }} ⊢ WP fill K (n,If (#♭ true) e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,If _ _ _) _);eauto.
    intros; inv_head_step;eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[simpl;auto|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  Lemma wp_if_false K E e1 e2 n Φ :
    ▷ WP fill K (n,e2) @ E {{ Φ }} ⊢ WP fill K (n, If (#♭ false) e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,If _ _ _) _);eauto.
    intros; inv_head_step;eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[simpl;auto|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  Lemma wp_fst K E e1 e2 v1 n Φ `{!IntoVal (n,e1) v1, !AsVal (n,e2)} :
    ▷ WP fill K (n,e1) @ E {{ Φ }}
      ⊢ WP fill K (n,Fst (Pair e1 e2)) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,Fst _) _);eauto.
    inv_head_step. eauto. intros. inv_head_step. eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  Lemma wp_snd K E e1 e2 n v2 Φ `{!AsVal (n,e1), !IntoVal (n,e2) v2} :
    ▷ WP fill K (n,e2) @ E {{ Φ }}
      ⊢ WP fill K (n, Snd (Pair e1 e2)) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,Snd _) _);eauto.
    inv_head_step. eauto. intros. inv_head_step. eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  Lemma wp_mask K E l n Φ :
    ▷ WP fill K (n,Loc borrow l) @ E {{ Φ }}
      ⊢ WP fill K (n, Mask (Loc global l)) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,Mask _) _);eauto.
    inv_head_step. eauto. intros. inv_head_step. eauto.
    { intros. iIntros "Hs". iApply (bnextgen_extensional_eq _ id);[resolve_next_state|].
      iApply nextgen_id. iFrame. }
    iNext. iIntros "H1".
    iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
    iApply nextgen_id. inv_head_step. iFrame.
  Qed.

  (** ------------------------------------------------------------ *)
  (** ------------------------ Allocations ----------------------- *)
  (** ------------------------------------------------------------ *)

  Lemma wp_stack_alloc K E n e v Φ `{!IntoVal (n,e) (n,v)} :
    0 < n -> (* stack is non empty *)
    scope v 0 ->
    ▷ (∀ l, [size] n ∗ (n - 1) @@ l ↦ v -∗ WP fill K (n,Loc (local 0) l) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (n,Salloc e) @ E {{ Φ }}.
  Proof.
    iIntros (Hlt scope) "[HΦ >Hsize]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "Hstate".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iDestruct (stacksize_own_agree_ng with "Hsize Hstate") as %Hsize. simpl in Hsize.
    assert (is_Some (s1 !! (length s1 - 1))) as [s' Hs'].
    { apply lookup_lt_is_Some. lia. }
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. apply salloc_fresh;eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls".
    rewrite /insert /= PeanoNat.Nat.sub_0_r Hs' /state_trans_state insert_length /=.
    rewrite -/(state_trans_state (h1,s1)). (* rewrite -/(state_interp (h1,s1) ns κs nt). *)
    iDestruct (gen_heap_alloc_stack_ng (h1,s1) ns κs nt l v0 with "Hstate") as ">[Hstate Hl]".
    { simpl. eauto. }
    { simpl. rewrite list_to_gmap_stack_lookup. rewrite /lookup_stack /= in H11.
      rewrite PeanoNat.Nat.sub_0_r in H11. auto. }
    rewrite /insert /insert_state_Insert /insert_state /= PeanoNat.Nat.sub_0_r /= Hs' /=.
    iDestruct "Hstate" as "[? [? ?]]". rewrite insert_length. iFrame.
    iModIntro.
    iSplitR "HΦ Hsize Hp Hl".
    all: iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
    all: iApply nextgen_id. iFrame. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_heap_alloc K E n e v Φ `{!IntoVal (n,e) (n,v)} :
    permanent v ->
    ▷ (∀ l, l ↦ v -∗ WP fill K (n,Loc global l) @ E {{ Φ }})
      ⊢ WP fill K (n,Halloc e) @ E {{ Φ }}.
  Proof.
    iIntros (Hperm) "HΦ".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hs & Hn)".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. apply halloc_fresh;eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls".
    iMod (gen_heap_alloc _ l v0 with "Hh") as "[Hh [Hl _]]";[auto|].
    iDestruct ("HΦ" with "Hl") as "Hwp".
    iModIntro. iFrame.
    iSplitR "Hwp".
    - iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
    - iFrame. iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
  Qed.

  (** ------------------------------------------------------------ *)
  (** ---------------------- Load and Store ---------------------- *)
  (** ------------------------------------------------------------ *)

  Lemma wp_heap_load K E l δ n v Φ :
    heap_tag δ ->
    ▷ (l ↦ v -∗ WP fill K (n,of_val v) @ E {{ Φ }})
      ∗ ▷ l ↦ v
      ⊢ WP fill K (n,Load (Loc δ l)) @ E {{ Φ }}.
  Proof.
    iIntros (Hδ) "[HΦ >Hl]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hs & Hn)".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hlookup.
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. constructor;eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step.
    2: { inversion Hδ. }
    rewrite /lookup_heap /= Hlookup in H10. simplify_eq.
    iMod "Hcls".
    iDestruct ("HΦ" with "Hl") as "Hwp".
    iModIntro. iFrame.
    iSplitR "Hwp".
    - iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
    - iFrame. iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
  Qed.

  Lemma wp_stack_load K E l j v n Φ :
    scope_tag (local j) ->
    ▷ ([size] n ∗ (n - 1 - Z.abs_nat j) @@ l ↦ v -∗ WP fill K (n,of_val (shift_val v j)) @ E {{ Φ }})
      ∗ ▷ (n - 1 - Z.abs_nat j) @@ l ↦ v
      ∗ ▷ [size] n
      ⊢ WP fill K (n,Load (Loc (local j) l)) @ E {{ Φ }}.
  Proof.
    iIntros (Hscope) "[HΦ [>Hl >Hsize] ]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hs & Hn)".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iDestruct (stacksize_own_agree with "[$]") as %Hsize;subst n.
    iDestruct (gen_stack_valid _ h1 with "Hl Hs") as %Hlookup.
    assert (is_Some (s1 !! (length s1 - 1 - Z.abs_nat j))) as [s0 Hs0].
    { rewrite /lookup /lookup_state_Lookup /lookup_state /lookup_stack /= in Hlookup.
      destruct (s1 !! (length s1 - 1 - Z.abs_nat j));eauto. done. }
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. eapply LoadStackS;eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. inversion H11.
    iMod "Hcls". 
    iModIntro. iDestruct ("HΦ" with "[$]") as "Hwp".
    iFrame.
    iSplitR "Hwp".
    - iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
    - iFrame. iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
  Qed.

  Lemma wp_heap_store K E e l δ v Φ `{!IntoVal (n,e) (n,v)} :
    permanent v ->
    heap_tag δ ->
    ▷ (l ↦ v -∗ WP fill K (n,lang.Unit) @ E {{ Φ }})
      ∗ ▷ l ↦ -
      ⊢ WP fill K (n,Store (Loc δ l) e) @ E {{ Φ }}.
  Proof.
    iIntros (Hperm Hδ) "[HΦ >Hl]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hs & Hn)".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iDestruct "Hl" as (w) "Hl".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hlookup.
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. constructor;auto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step.
    2: { inversion Hδ. }
    iMod "Hcls".
    iMod (gen_heap_update _ _ _ v0 with "Hh Hl") as "[Hh Hl]".
    iDestruct ("HΦ" with "Hl") as "Hwp".
    iModIntro. iFrame.
    iSplitR "Hwp".
    - iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
    - iFrame. iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
  Qed.

  Lemma wp_stack_store K E e l j v v' w Φ `{!IntoVal (n,e) (n,v)} :
    scope v j ->
    shift_val v (Z.abs_nat j) = v' ->
    ▷ ([size] n ∗ (n - 1 - Z.abs_nat j) @@ l ↦ v -∗ WP fill K (n,lang.Unit) @ E {{ Φ }})
      ∗ ▷ (n - 1 - Z.abs_nat j) @@ l ↦ w
      ∗ ▷ [size] n
      ⊢ WP fill K (n,Store (Loc (local j) l) e) @ E {{ Φ }}.
  Proof.
    iIntros (Hperm Hδ) "[HΦ [>Hl >Hsize] ]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hs & Hn)".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iDestruct (stacksize_own_agree with "[$]") as %Hsize;subst n.
    iDestruct (gen_stack_valid _ h1 with "Hl Hs") as %Hlookup.
    assert (is_Some (s1 !! (length s1 - 1 - Z.abs_nat j))) as [s0 Hs0].
    { rewrite /lookup /lookup_state_Lookup /lookup_state /lookup_stack /= in Hlookup.
      destruct (s1 !! (length s1 - 1 - Z.abs_nat j));eauto. done. }
    iSplit.
    { iPureIntro. exists NormalMode. do 5 econstructor;[constructor|].
      simpl. eapply StoreStackS;eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. inversion H13.
    iMod "Hcls". 
    iMod (gen_stack_update _ _ _ _ _ v0 with "Hl Hs") as "[Hl Hs]";eauto.
    rewrite /insert /insert_state_Insert /insert_state /insert_stack /= Hs0.
    iModIntro. iDestruct ("HΦ" with "[$]") as "Hwp".
    iFrame.
    iSplitR "Hwp".
    - iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame. rewrite insert_length. iFrame.
    - iFrame. iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
      iApply nextgen_id. iFrame.
  Qed.

  (** ------------------------------------------------------------ *)
  (** ----------------------- Control Flow ----------------------- *)
  (** ------------------------------------------------------------ *)
    
  (** Control flow -- stateful due to stack frames *)
  Lemma wp_call_global K E n k x e1 e2 v2' v2 Φ `{!IntoVal (n,e2) (n,v2)} :
    shift_val v2 (-1) = v2' ->
    ▷ ([size] (S n) -∗ WP fill K (S n,Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1))) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (n,Call (Lam global k x e1) e2) @ E {{ Φ }}.
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
    rewrite /gen_stack_interp.
    rewrite list_to_gmap_stack_push_stack push_stack_length.
    iFrame.
    iSplitR "HΦ Hs".
    all: iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
    all: iApply nextgen_id. iFrame. rewrite PeanoNat.Nat.add_1_r. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_call_local K E n (i : Z) k x e1 e2 e1' v2' v2 Φ `{!IntoVal (n,e2) (n,v2)} :
    scope_tag (local i) ->
    shift_expr e1 (i - 1) = e1' ->
    shift_val v2 (-1) = v2' ->
    ▷ ([size] (S n) -∗ WP fill K (S n, Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1'))) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (n, Call (Lam (local i) k x e1) e2) @ E {{ Φ }}.
  Proof.
    iIntros (Hscope Hshift1 Hshift2) "[HΦ >Hs]".
    iApply wp_lift_nonthrow_head_step; auto.
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$]") as %Heq;subst.
    iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. inversion Hscope;subst;auto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls". iModIntro.
    rewrite /gen_stack_interp list_to_gmap_stack_push_stack push_stack_length. iFrame.
    iSplitR "HΦ Hs".
    all: iApply (bnextgen_extensional_eq _ id);[resolve_next_state;simpl;auto|].
    all: iApply nextgen_id. iFrame. rewrite PeanoNat.Nat.add_1_r. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_return K K' E n i e v Φ `{!IntoVal (n,e) v} :
    (i <= 0)%Z ->
    Z.abs_nat i <= n ->
    ▷ ([size] (n - (Z.abs_nat i)) -∗ ⚡={trans_single stack_gname (state_trans (n - (Z.abs_nat i)))}=> WP fill K' (n - (Z.abs_nat i),shift_expr e i) @ E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ WP fill K (n,Return (Cont i K') e) @ E {{ Φ }}.
  Proof.
    iIntros (Hle Hlen) "[HΦ >Hn]".
    iApply wp_lift_throw_head_step;auto.
    iIntros ([h1 s1] ns κ κs nt) "Hstate".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iDestruct (stacksize_own_agree_ng with "Hn Hstate") as %Hsize. simpl in Hsize.
    iSplit.
    { iPureIntro. inv_head_step. repeat econstructor;eauto. }
    iNext. iIntros (r0 σ2 efs Hstep) "Hp".
    inv_head_step. iMod "Hcls". rewrite H1.
    iDestruct "Hstate" as "(Hh & Hs & Hsize)".
    iDestruct (gen_stack_interp_stack_pop with "Hs") as "Hs";[eauto|].
    iDestruct (gen_heap_interp_stack_pop _ (length s1 - Z.abs_nat i) with "Hh") as "Hh".
    iMod (stacksize_own_update (length s1 - Z.abs_nat i) with "[$Hsize $Hn]") as "[Hsize Hn]".
    iDestruct (stack_size_auth_stack_pop _ (length s1 - Z.abs_nat i) with "Hsize") as "Hsize".
    iModIntro.
    iDestruct ("HΦ" with "Hn") as "Hwp". iFrame.
    iSplitR "Hwp".
    - iApply bnextgen_extensional_eq;[resolve_next_state|].
      iModIntro. iFrame. rewrite popN_stack_length. iFrame.
    - iApply bnextgen_extensional_eq;[resolve_next_state|].
      iModIntro. rewrite /CC_ectxi_language.fill /= fill_proj_eq. iFrame.
  Qed.


End lifting.
