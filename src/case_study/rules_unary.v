From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting weakestpre gen_heap_lifting.
From nextgen.case_study Require Export stack_lang stack_transform.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From nextgen Require Import nextgen_basic gen_trans gmap_view_transformation nextgen_id.
From nextgen Require Export nextgen_pointwise.
Set Default Proof Using "Type".
Import uPred.
From nextgen.lib Require Import wsat fancy_updates.


(** Basic rules for language operations. *)

(* CMRA for size *)
Class stacksizeGS (Σ : gFunctors) (Ω : gTransformations Σ) := StackSizeGS {
  heapG_stacksize_name : gname;
  heapG_excl_nat_stacksizeGS :> genIndInG Σ Ω (excl_authUR natR)
}.


Inductive locality_lifetime : Type :=
  | lifetime_stack : nat -> locality_lifetime
  | lifetime_heap : locality_lifetime.

Definition locality_lifetime_rel : relation locality_lifetime :=
  λ l1 l2, match l1,l2 with
           | lifetime_heap, _ => True
           | lifetime_stack f1, lifetime_stack f2 => f1 <= f2
           | _,_ => False
           end.

Definition state_trans (n : nat) := (map_entry_lift_gmap_view (stack_location_cut n)).

Definition locality_pick (l : locality_lifetime) :=
  match l with
  | lifetime_heap => id
  | lifetime_stack n => state_trans n
  end.

Lemma pick_state_trans_eq (Σ : gFunctors) (Ω : gTransformations Σ) `{!inG Σ (gmap_view.gmap_viewR (nat * loc) (leibnizO val))} (n : nat) :
  transmap_insert_inG (state_trans n) Ω = transmap_insert_inG (locality_pick (lifetime_stack n)) Ω.
Proof. auto. Qed.

Global Instance locality_lifetime_rel_pre : PreOrder locality_lifetime_rel.
Proof.
  split.
  - intros l. destruct l;simpl;auto.
  - intros l1 l2 l3 Hl1 Hl2.
    destruct l1,l2,l3;try by inversion Hl1;try by inversion Hl2.
    simpl in *. lia.
Qed.

Global Instance locality_lifetime_cmra_morphism : ∀ l, CmraMorphism (locality_pick l) :=
  λ l, match l with
       | lifetime_heap => cmra_morphism_id
       | lifetime_stack n => gMapTrans_lift_CmraMorphism (stack_location_cut n)
       end.

Global Instance locality_lifetime_rel_dec : ∀ l1 l2, Decision (locality_lifetime_rel l1 l2).
Proof. intros l1 l2. destruct l1,l2;simpl;[apply _|right;auto|left;auto..]. Qed.

Global Instance locality_lifetime_pick
  : pick_transform_preorder (gmap_view.gmap_viewR (nat * loc) (leibnizO val)) :=
  { C := locality_lifetime;
    CR := locality_lifetime_rel;
    C_pick := locality_pick;
  }.

Notation inv_pick_transform := (@inv_pick_transform _ locality_lifetime_pick).

(* CMRA for state interpretation *)
Class heapGS (Σ : gFunctors) (Ω : gTransformations Σ) := HeapGS {
  heapG_invGS : invGIndS_gen HasNoLc Σ Ω _ locality_lifetime_pick;
  (* heapG_no_trans :> noTransInG Σ Ω (gmap_view.gmap_viewR (nat * loc) (leibnizO val)); *)
  heapG_gen_heapGS :> gen_heapIndGS loc val Σ Ω;
  heapG_gen_stackGS :> gen_heapNoGS (nat * loc) val Σ Ω; (* gen_heapNoMetaGS (nat * loc) val Σ Ω ; *)
  heapG_stacksizeGS :> stacksizeGS Σ Ω
}.

Section StackSize.
  Context `{!stacksizeGS Σ Ω}.

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

#[global] Instance heapG_inv_transform_inG `{H:heapGS Σ Ω} : inG Σ (gmap_view.gmap_viewR positive (optionO (leibnizO C))) :=
  ((((heapG_invGS.(invGS_wsat)).(wsat_inG)).(wsatGpreS_func)).(noTransInG_A_inG)).(noTransInG_inG).

(* #[global] Instance gmap_view_inG `{H:heapGS Σ Ω} : ghost_mapNoG Σ Ω (nat * loc) (leibnizO val) := *)
(*   @GhostMapNoG Σ Ω (nat * loc) (leibnizO val) _ _ *)
(*     (((heapG_invGS.(invGS_wsat)).(wsat_inG)).(wsatGpreS_func)).(noTransInG_B_inG). *)

#[global] Instance gmap_view_inG `{H:invGIndS_gen fancy_updates.HasNoLc Σ Ω (gmap_view.gmap_viewR (nat * loc) (leibnizO val))} : ghost_mapNoG Σ Ω (nat * loc) (leibnizO val) :=
  @GhostMapNoG Σ Ω (nat * loc) (leibnizO val) _ _
    ((invGS_wsat.(wsat_inG)).(wsatGpreS_func)).(noTransInG_B_inG).
  (* @GhostMapNoG Σ Ω (nat * loc) (leibnizO val) _ _ *)
  (*   (wsatGpreS_func).(noTransInG_B_inG). *)

#[global] Instance heapG_wsatpre `{H:heapGS Σ Ω} : invGIndS_gen fancy_updates.HasNoLc Σ Ω (gmap_view.gmap_viewR (nat * loc) (leibnizO val)) locality_lifetime_pick :=
  heapG_invGS.

#[global] Instance heapG_gen_heapGS_inG `{H:heapGS Σ Ω} : gen_heapGS (nat * loc) val Σ :=
  @into_gen_heap_from_no (nat * loc) val Σ Ω _ _ _ heapG_gen_stackGS.


(* Definition state_trans_aux : seal (@state_trans_def). *)
(* Proof. by eexists. Qed. *)
(* Definition state_trans := (state_trans_aux).(unseal). *)
(* Local Definition state_trans_unseal : *)
(*   @state_trans = @state_trans_def := state_trans_aux.(seal_eq). *)

Definition state_trans_state (σ : state) := state_trans (length σ.2).
Definition stack_gname `{heapGS Σ} : gname := heapG_gen_stackGS.(no_gen_heap_name).

Definition next_choose_f (e : stack_expr) : option locality_lifetime :=
  (find_i e.2) ≫= λ i, Some (lifetime_stack (e.1 - Z.abs_nat i)).

(* Definition next_state_f_aux : seal (@next_state_f_def). *)
(* Proof. by eexists. Qed. *)
(* Definition next_state_f := (next_state_f_aux).(unseal). *)
(* Local Definition next_state_f_unseal : *)
(*   @next_state_f = @next_state_f_def := next_state_f_aux.(seal_eq). *)
(* Global Arguments next_state_f {Σ Ω H} e. *)

(* #[global] *)
(* Instance next_state_f_cmra_morphism : ∀ (Σ : gFunctors) (Ω : gTransformations Σ) (e : nat), CmraMorphism (next_state_f e). *)
(* Proof. apply _. *)
(*   intros. rewrite /next_state_f. *)
(*   destruct (find_i e.2);apply _. *)
(* Qed. *)

(* #[global] *)
(* Instance state_trans_cmra_morphism : ∀ (Σ : gFunctors) (Ω : gTransformations Σ) n, *)
(*  CmraMorphism (state_trans n). *)
(* Proof. *)
(*   intros. rewrite /state_trans /=. apply _. *)
(* Qed. *)

Definition gen_stack_interp `{H : heapGS Σ Ω} s :=
  @ghost_map.ghost_map_auth Σ _ _ _ _ _ (stack_gname) 1 (list_to_gmap_stack s).

Instance heapG_irisGS `{heapGS Σ Ω} : irisGS_gen _ lang Σ Ω (gmap_view.gmap_viewR (nat * loc) (leibnizO val)) := {
    iris_invGS := heapG_invGS;
    state_interp σ _ _ _ :=
      let '(h,s) := σ in
      (gen_heap_interp h
         ∗ (* gen_heap_interp (list_to_gmap_stack s) *) gen_stack_interp s
         ∗ own heapG_stacksize_name (excl_auth_auth (length s)))%I;
    next_choose := next_choose_f;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := (entails_po).(PreOrder_Reflexive) _
  }.
Global Opaque iris_invGS.

Definition id := (id : (gmap_view.gmap_viewR (nat * loc) (leibnizO val)) -> (gmap_view.gmap_viewR (nat * loc) (leibnizO val))).

#[global]
Instance option_state_trans_cmra_morphism `{H : heapGS Σ Ω} (n : option locality_lifetime) : CmraMorphism (from_option (λ n, locality_pick n) id n) 
  := match n with
     | None => _
     | Some n => _
     end.

Definition next_state_def {Σ} (Ω : gTransformations Σ) `{H : heapGS Σ Ω} (n: locality_lifetime) :=
  transmap_insert_inG (locality_pick n) Ω.
Definition next_state_aux : seal (@next_state_def).
Proof. by eexists. Qed.
Definition next_state := (next_state_aux).(unseal).
Local Definition next_state_unseal :
  @next_state = @next_state_def := next_state_aux.(seal_eq).
Global Arguments next_state {Σ} Ω {H} n.

Lemma next_state_eq `{H : heapGS Σ Ω} n :
  next_state Ω n = transmap_insert_inG (locality_pick n) Ω.
Proof.
  rewrite next_state_unseal /next_state_def /= //.
Qed.

Lemma next_state_eq' `{H : heapGS Σ Ω} n :
  next_state Ω (lifetime_stack n) = transmap_insert_inG (state_trans n) Ω.
Proof.
  rewrite next_state_unseal /next_state_def /= //. 
Qed.

Definition next_state_inv_def {Σ} (Ω : gTransformations Σ) `{H : heapGS Σ Ω} (n: locality_lifetime) :=
  transmap_insert_inG (inv_pick_transform n) Ω.
Definition next_state_inv_aux : seal (@next_state_inv_def).
Proof. by eexists. Qed.
Definition next_state_inv := (next_state_inv_aux).(unseal).
Local Definition next_state_inv_unseal :
  @next_state_inv = @next_state_inv_def := next_state_inv_aux.(seal_eq).
Global Arguments next_state_inv {Σ} Ω {H} n.

Lemma next_state_inv_eq `{H : heapGS Σ Ω} n :
  next_state_inv Ω n = transmap_insert_inG (inv_pick_transform n) Ω.
Proof.
  rewrite next_state_inv_unseal /next_state_inv_def /= //.
Qed.

Lemma next_state_inv_eq' `{H : heapGS Σ Ω} n :
  next_state_inv Ω n = transmap_insert_inG (inv_pick_transform n) Ω.
Proof.
  rewrite next_state_inv_unseal /next_state_inv_def /= //. 
Qed.
  
#[global]
Instance heapG_next_monotone `{heapGS Σ Ω} : NextMonotone.
Proof.
  constructor. intros. simpl in *.
  unfold CC_ectxi_language.fill.
  destruct e1;simpl in *. rewrite /stack_to_val in H0.
  simpl in H0.
  destruct (to_val e) eqn:He;try done.
  unfold next_choose_f. rewrite fill_proj /=.
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

Notation "⚡={ Ω <- n }=> P" := (⚡={ next_state_inv Ω n }=> ⚡={ next_state Ω n }=> P)%I
  (at level 99, Ω at level 50, n at level 50, P at level 200, format "⚡={ Ω  <-  n }=>  P") : bi_scope.

Section heapG_nextgen_updates.
  Context `{heapGS Σ Ω}.

  Lemma stacksize_own_agree_ng n σ ns κs nt :
    [size] n -∗ state_interp σ ns κs nt -∗ ⌜n = (length σ.2)⌝.
  Proof.
    iIntros "Hs Hσ". destruct σ as [h' s'].
    simpl. iDestruct "Hσ" as "(Hh & Hstk & Hsize) /=".
    iDestruct (stacksize_own_agree with "[$Hsize $Hs]") as %Hs;auto.
  Qed.

  Lemma gen_heap_alloc_stack_ng (σ : language.state (CC_ectx_lang stack_expr)) ns κs nt l v :
    is_Some (σ.2 !! (length σ.2 - 1)) ->
    (list_to_gmap_stack σ.2) !! ((length σ.2 - 1),l) = None ->
    state_interp σ ns κs nt ==∗
    state_interp (<[ 0 @ l := v ]> σ) ns κs nt ∗ (length σ.2 - 1) @@ l ↦ v.
  Proof.
    iIntros ([s0 Hs0] Hnone) "Hstate".
    destruct σ as [h1 s1]. simpl snd in *.
    iDestruct "Hstate" as "(Hh & Hstk & Hsize)".
    iDestruct (ghost_map.ghost_map_insert _ v with "Hstk") as ">[Hstk Hl]";[eauto|].
    rewrite (list_to_gmap_stack_insert _ s0)//.
    simpl. rewrite /insert /insert_state_Insert /=.
    rewrite PeanoNat.Nat.sub_0_r Hs0 insert_length. iFrame.
    rewrite /mapsto seal_eq /gen_heap.mapsto_def /=. rewrite /stack_gname. simpl. iFrame. simpl. iFrame.
    done.
  Qed.

  Lemma gen_stack_valid (s : stack) (h : heap) (j : nat) (l : loc) (w : val) :
    (length s - 1 - j) @@ l ↦ w -∗ gen_stack_interp s -∗ ⌜[[ (h,s) @ j ]] !! l = Some w ⌝.
  Proof.
    iIntros "Hl Hs".
    rewrite /mapsto seal_eq /=.
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
    rewrite /mapsto seal_eq /=.
    iMod (ghost_map.ghost_map_update with "Hs Hl") as "[Hs Hl]". iFrame.
    erewrite list_to_gmap_stack_insert =>//.
  Qed.

  Lemma gen_stack_interp_stack_pop s1 i
    (Hlen: length s1 ≥ i) :
    gen_stack_interp s1 ⊢
    ⚡={next_state Ω (lifetime_stack ((length s1) - i))}=> gen_stack_interp (popN_stack s1 i).
  Proof.
    iIntros "Hs". rewrite /gen_stack_interp /=.
    rewrite /ghost_map.ghost_map_auth seal_eq /ghost_map.ghost_map_auth_def /=.
    rewrite next_state_unseal /next_state_def /=.
    iDestruct (transmap_own_insert_right (state_trans (length s1 - i)) with "Hs") as "Hs".
    iApply (bnextgen_mono with "Hs").
    rewrite /state_trans
      /map_entry_lift_gmap_view /= /cmra_morphism_extra.fmap_view /= /cmra_morphism_extra.fmap_pair /=.
    rewrite /gMapTrans_frag_lift map_imap_empty /=.
    rewrite /gmap_view.gmap_view_auth /view_auth.
    rewrite agree_map_to_agree.
    rewrite stack_location_cut_popN_stack. iIntros "Hs". iFrame.
  Qed.

  Lemma gen_stack_interp_stack_pop_inv s1 i
    (Hlen: length s1 ≥ i) :
    gen_stack_interp s1 ⊢
    ⚡={next_state_inv Ω (lifetime_stack ((length s1) - i))}=> gen_stack_interp s1.
  Proof.
    iIntros "Hs".
    rewrite /gen_stack_interp /=.
    rewrite /ghost_map.ghost_map_auth seal_eq /ghost_map.ghost_map_auth_def /=.
    rewrite next_state_inv_unseal /next_state_inv_def /=.
    iDestruct (transmap_own_insert_other_right (inv_pick_transform (lifetime_stack (length s1 - i))) with "Hs") as "Hs".
    iApply (bnextgen_mono with "Hs"). iIntros "Hs". iFrame.
  Qed.

  Lemma gen_stack_interp_heap_inv s1 i
    (Hlen: length s1 ≥ i) :
    gen_stack_interp s1 ⊢
    ⚡={next_state_inv Ω lifetime_heap}=> gen_stack_interp s1.
  Proof.
    iIntros "Hs".
    rewrite /gen_stack_interp /=.
    rewrite /ghost_map.ghost_map_auth seal_eq /ghost_map.ghost_map_auth_def /=.
    rewrite next_state_inv_unseal /next_state_inv_def /=.
    iModIntro. iFrame.
  Qed.
  
  Lemma stack_size_auth_intro (s : nat) n :
    own heapG_stacksize_name (excl_auth_auth s) ⊢
    ⚡={next_state Ω n}=> own heapG_stacksize_name (excl_auth_auth s).
  Proof.
    iIntros "Hs". rewrite next_state_unseal /next_state_def.
    iModIntro. iFrame.
  Qed.

  Lemma stack_size_auth_inv_intro (s : nat) n :
    own heapG_stacksize_name (excl_auth_auth s) ⊢
    ⚡={next_state_inv Ω n}=> own heapG_stacksize_name (excl_auth_auth s).
  Proof.
    iIntros "Hs". rewrite next_state_inv_unseal /next_state_inv_def.
    iModIntro. iFrame.
  Qed.

  Lemma stack_size_frag_intro (s : nat) n :
    [size] s ⊢
    ⚡={next_state Ω n}=> [size] s.
  Proof.
    iIntros "Hs". rewrite next_state_unseal /next_state_def.
    iModIntro. iFrame.
  Qed.

  Lemma stack_size_frag_inv_intro (s : nat) n :
    [size] s ⊢
    ⚡={next_state_inv Ω n}=> [size] s.
  Proof.
    iIntros "Hs". rewrite next_state_inv_unseal /next_state_inv_def.
    iModIntro. iFrame.
  Qed.
  
  Lemma heap_stack_intro (l : loc) (q : dfrac) (v : val) n :
    l ↦{q} v ⊢ ⚡={next_state Ω n}=> l ↦{q} v.
  Proof.
    iIntros "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def
      next_state_unseal /next_state_def.
    iModIntro. iFrame.
  Qed.

  Lemma heap_stack_inv_intro (l : loc) (q : dfrac) (v : val) n :
    l ↦{q} v ⊢ ⚡={next_state_inv Ω n}=> l ↦{q} v.
  Proof.
    iIntros "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def
      next_state_inv_unseal /next_state_inv_def.
    iModIntro. iFrame.
  Qed.

  Lemma gen_heap_interp_stack_pop (h1 : heap) n :
    gen_heap_interp h1 ⊢
    ⚡={next_state Ω n}=> gen_heap_interp h1.
  Proof.
    iIntros "Hg". iDestruct "Hg" as (m Hdom) "[Hg Hmeta]".
    rewrite /gen_heap_interp /ghost_map.ghost_map_auth !seal_eq /= /ghost_map.ghost_map_auth_def
      next_state_unseal /next_state_def.
    iModIntro. iExists _. iFrame. auto.
  Qed.

  Lemma gen_heap_interp_stack_pop_inv (h1 : heap) n :
    gen_heap_interp h1 ⊢
    ⚡={next_state_inv Ω n}=> gen_heap_interp h1.
  Proof.
    iIntros "Hg". iDestruct "Hg" as (m Hdom) "[Hg Hmeta]".
    rewrite /gen_heap_interp /ghost_map.ghost_map_auth !seal_eq /= /ghost_map.ghost_map_auth_def
      next_state_inv_unseal /next_state_inv_def.
    iModIntro. iExists _. iFrame. auto.
  Qed.

  Lemma later_credits_intro m n :
    £ m ⊢ ⚡={next_state Ω n}=> £ m.
  Proof.
    iIntros "Hm".
    rewrite next_state_unseal /next_state_def.
    iDestruct (wsat.lc_ind_insert_intro _ (locality_pick n) with "Hm") as "Hm".
    iApply (bnextgen_mono with "Hm"). iIntros "$". 
  Qed.

  Lemma later_credits_inv_intro m n :
    £ m ⊢ ⚡={next_state_inv Ω n}=> £ m.
  Proof.
    iIntros "Hm".
    rewrite next_state_inv_unseal /next_state_inv_def.
    iDestruct (wsat.lc_ind_insert_intro _ (inv_pick_transform n) with "Hm") as "Hm".
    iApply (bnextgen_mono with "Hm"). iIntros "$". 
  Qed.

  Lemma stack_stack_pop_intro i l q v n
    (Hlt : i < n) :
    i @@ l ↦{q} v ⊢ ⚡={next_state Ω (lifetime_stack n)}=> i @@ l ↦{q} v.
  Proof.
    iIntros "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def
      next_state_unseal /next_state_def.
    rewrite -/stack_gname.
    iModIntro. simpl.
    rewrite /state_trans /map_entry_lift_gmap_view /gmap_view.gmap_view_frag /=.
    rewrite /cmra_morphism_extra.fmap_view /=.
    rewrite /gMapTrans_frag_lift /=.
    rewrite map_imap_insert /= agree_option_map_to_agree /=.
    rewrite /stack_location_cut bool_decide_true // /=.
  Qed.

  Lemma stack_stack_pop_inv_intro i l q v n :
    i @@ l ↦{q} v ⊢ ⚡={next_state_inv Ω n}=> i @@ l ↦{q} v.
  Proof.
    iIntros "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def
      next_state_inv_unseal /next_state_inv_def.
    rewrite -/stack_gname.
    iModIntro. iFrame.
  Qed.

  Lemma stack_heap_intro i l q v :
    i @@ l ↦{q} v ⊢ ⚡={next_state Ω lifetime_heap}=> i @@ l ↦{q} v.
  Proof.
    iIntros "Hl".
    rewrite /mapsto seal_eq /gen_heap.mapsto_def
      /ghost_map.ghost_map_elem seal_eq /ghost_map.ghost_map_elem_def
      next_state_unseal /next_state_def.
    iModIntro. iFrame.
  Qed.

  (* The following two instances make typeclass resolution much faster *)
  Lemma next_state_id n P :
    ((⚡={next_state Ω n}=> P) ⊢ ⚡={next_state Ω n}=> P).
  Proof. intros. auto. Qed.
  Lemma next_state_inv_id n P :
    ((⚡={next_state_inv Ω n}=> P) ⊢ ⚡={next_state_inv Ω n}=> P).
  Proof. intros. auto. Qed.
  
  Lemma next_state_pure_intro P n :
    (■ P) ⊢ ⚡={next_state Ω n}=> ■ P.
  Proof.
    iIntros "Hp". iApply bnextgen_intro_plainly. eauto.
  Qed.
  Lemma next_state_pure_inv_intro P n :
    (■ P) ⊢ ⚡={next_state_inv Ω n}=> ■ P.
  Proof.
    iIntros "Hp". iApply bnextgen_intro_plainly. eauto.
  Qed.

  (* #[global] Instance gen_stack_interp_stack_pop' s1 i (Hlen: length s1 >= i) *)
  (*   : IntoPnextgen _ _ _ := gen_stack_interp_stack_pop s1 i Hlen. *)
  (* #[global] Instance stack_size_auth_intro' s n *)
  (*   : IntoPnextgen _ _ _ := stack_size_auth_intro s n. *)
  #[global] Instance stack_size_frag_intro' s n
    : IntoPnextgen _ _ _ := stack_size_frag_intro s n.
  #[global] Instance stack_size_frag_inv_intro' s n
    : IntoPnextgen _ _ _ := stack_size_frag_inv_intro s n.
  #[global] Instance heap_stack_intro' (l : loc) (q : dfrac) (v : val) n
    : IntoPnextgen _ _ _ := heap_stack_intro l q v n.
  #[global] Instance heap_stack_inv_intro' (l : loc) (q : dfrac) (v : val) n
    : IntoPnextgen _ _ _ := heap_stack_inv_intro l q v n.
  #[global] Instance stack_stack_pop_inv_intro' i l q v n 
    : IntoPnextgen _ _ _ := stack_stack_pop_inv_intro i l q v n.
  #[global] Instance stack_heap_intro' i l q v
    : IntoPnextgen _ _ _ := stack_heap_intro i l q v.
  (* #[global] Instance gen_heap_interp_stack_pop' (h1 : heap) n *)
  (*   : IntoPnextgen _ _ _ := gen_heap_interp_stack_pop h1 n. *)
  (* #[global] Instance stack_stack_pop_intro' i l q v n Hlt *)
  (*   : IntoPnextgen _ _ _ := stack_stack_pop_intro i l q v n Hlt. *)
  #[global] Instance later_credits_intro' m n
    : IntoPnextgen _ _ _ := later_credits_intro m n.
  #[global] Instance later_credits_inv_intro' m n
    : IntoPnextgen _ _ _ := later_credits_inv_intro m n.

  #[global] Instance next_state_id' n P
    : IntoPnextgen _ _ _ := next_state_id n P.
  #[global] Instance next_state_pure_intro' P n
    : IntoPnextgen _ _ _ := next_state_pure_intro P n.
  #[global] Instance next_state_inv_id' n P
    : IntoPnextgen _ _ _ := next_state_inv_id n P.
  #[global] Instance next_state_pure_inv_intro' P n
    : IntoPnextgen _ _ _ := next_state_pure_inv_intro P n.
  
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

  (* Lemma next_state_letin_id n x e1 v1 e2 `{!IntoVal (n,e1) v1} : *)
  (*   next_state_f (n, LetIn x e1 e2) = id. *)
  (* Proof. *)
  (*   inv_head_step. *)
  (*   rewrite /next_state_f /find_i /=. *)
  (*   by erewrite construct_ctx_to_val;[|apply to_of_val]. *)
  (* Qed. *)

  (* Ltac resolve_next_state := *)
  (*        match goal with *)
  (*        | |- ∀ x, next_choose_f _ _ = _ _ => *)
  (*            inv_head_step; rewrite /next_choose_f /find_i /=; (try rewrite !to_of_val); (try rewrite construct_ctx_of_val /=); (try rewrite !to_of_val); simpl; auto *)
  (*        | |- ∀ x, next_state _ _ = _ _ => *)
  (*            inv_head_step; rewrite /next_state /next_choose_f /find_i /=; (try rewrite !to_of_val); (try rewrite construct_ctx_of_val /=); (try rewrite !to_of_val); simpl; auto *)
  (*        end. *)

   Ltac resolve_next_state :=
         match goal with
         | |- context [ (?={ ?Ω <- ?e }=> ?P)%I ] =>
             rewrite /bnextgen_option; simpl next_choose; inv_head_step; rewrite /next_choose_f /find_i /=; (try rewrite !to_of_val); (try rewrite construct_ctx_of_val /=); (try rewrite !to_of_val); simpl
         end.

  Notation id := (id : (gmap_view.gmap_viewR (nat * loc) (leibnizO val)) -> (gmap_view.gmap_viewR (nat * loc) (leibnizO val))).

  Lemma wp_LetIn K E e1 e2 v1 x Φ (n : nat) `{!IntoVal (n,e1) v1} :
                               ▷ (WP fill K (n,subst' x v1.2 e2) @ E {{ Φ }}) ⊢ WP fill K (n,LetIn x e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,LetIn _ _ _) _);eauto.
    intros; inv_head_step;eauto.
    { intros. iIntros "Hs". by resolve_next_state. }
    iNext. iIntros "H1". by resolve_next_state.
  Qed.

  Lemma wp_bin_op K E op e1 e2 n v1 v2 w Φ `{!IntoVal (n,e1) (n,v1), !IntoVal (n,e2) (n,v2)} :
    binop_eval op v1 v2 = Some w →
    ▷ (WP fill K (n, of_val w) @ E {{ Φ }})
      ⊢ WP fill K (n, BinOp op e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,BinOp op _ _) _);eauto.
    intros; inv_head_step;eauto.
    { intros. iIntros "Hs". by resolve_next_state. }
    iNext. iIntros "H1". by resolve_next_state.
  Qed.

  Lemma wp_if_true K E e1 e2 n Φ :
    ▷ (WP fill K (n,e1) @ E {{ Φ }}) ⊢ WP fill K (n,If (#♭ true) e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,If _ _ _) _);eauto.
    intros; inv_head_step;eauto.
  Qed.

  Lemma wp_if_false K E e1 e2 n Φ :
    ▷ (WP fill K (n,e2) @ E {{ Φ }}) ⊢ WP fill K (n, If (#♭ false) e1 e2) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,If _ _ _) _);eauto.
    intros; inv_head_step;eauto.
  Qed.

  Lemma wp_fst K E e1 e2 v1 n Φ `{!IntoVal (n,e1) v1, !AsVal (n,e2)} :
    ▷ (WP fill K (n,e1) @ E {{ Φ }})
      ⊢ WP fill K (n,Fst (Pair e1 e2)) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,Fst _) _);eauto.
    inv_head_step. eauto. intros; inv_head_step;eauto.
    { intros. iIntros "Hs". by resolve_next_state. }
    iNext. iIntros "H1". by resolve_next_state.
  Qed.

  Lemma wp_snd K E e1 e2 n v2 Φ `{!AsVal (n,e1), !IntoVal (n,e2) v2} :
    ▷ (WP fill K (n,e2) @ E {{ Φ }})
      ⊢ WP fill K (n, Snd (Pair e1 e2)) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,Snd _) _);eauto.
    inv_head_step. eauto. intros; inv_head_step;eauto.
    { intros. iIntros "Hs". by resolve_next_state. }
    iNext. iIntros "H1". by resolve_next_state.
  Qed.

  Lemma wp_mask K E l n Φ :
    ▷ (WP fill K (n,Loc borrow l) @ E {{ Φ }})
      ⊢ WP fill K (n, Mask (Loc global l)) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_nonthrow_pure_det_head_step_no_fork' K (n,Mask _) _);eauto.
    inv_head_step. eauto.
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
    resolve_next_state. iMod "Hcls".
    rewrite /insert /= PeanoNat.Nat.sub_0_r Hs' /state_trans_state insert_length /=.
    rewrite -/(state_trans_state (h1,s1)). (* rewrite -/(state_interp (h1,s1) ns κs nt). *)
    iDestruct (gen_heap_alloc_stack_ng (h1,s1) ns κs nt l v0 with "Hstate") as ">[Hstate Hl]".
    { simpl. eauto. }
    { simpl. rewrite list_to_gmap_stack_lookup. rewrite /lookup_stack /= in H11.
      rewrite PeanoNat.Nat.sub_0_r in H11. auto. }
    rewrite /insert /insert_state_Insert /insert_state /= PeanoNat.Nat.sub_0_r /= Hs' /=.
    iDestruct "Hstate" as "[? [? ?]]". rewrite insert_length. iFrame.
    iModIntro.
    iApply "HΦ". iFrame.
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
    resolve_next_state.
    iMod "Hcls".
    iMod (gen_heap_alloc _ l v0 with "Hh") as "[Hh [Hl _]]";[auto|].
    iDestruct ("HΦ" with "Hl") as "Hwp".
    iModIntro. iFrame.
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
    resolve_next_state.
    2: { inversion Hδ. }
    rewrite /lookup_heap /= Hlookup in H10. simplify_eq.
    iMod "Hcls".
    iDestruct ("HΦ" with "Hl") as "Hwp".
    iModIntro. iFrame.
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
    resolve_next_state. inversion H11.
    iMod "Hcls". 
    iModIntro. iDestruct ("HΦ" with "[$]") as "Hwp".
    iFrame.
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
    resolve_next_state.
    2: { inversion Hδ. }
    iMod "Hcls".
    iMod (gen_heap_update _ _ _ v0 with "Hh Hl") as "[Hh Hl]".
    iDestruct ("HΦ" with "Hl") as "Hwp".
    iModIntro. iFrame.
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
    resolve_next_state. inversion H13.
    iMod "Hcls". 
    iMod (gen_stack_update _ _ _ _ _ v0 with "Hl Hs") as "[Hl Hs]";eauto.
    rewrite /insert /insert_state_Insert /insert_state /insert_stack /= Hs0.
    iModIntro. iDestruct ("HΦ" with "[$]") as "Hwp".
    rewrite insert_length. iFrame.
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
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize)".
    iDestruct (stacksize_own_agree with "[$]") as %Heq;subst.
    iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    resolve_next_state. iMod "Hcls". iModIntro.
    rewrite /gen_stack_interp.
    rewrite list_to_gmap_stack_push_stack push_stack_length.
    rewrite PeanoNat.Nat.add_1_r. iFrame.
    by iApply "HΦ".
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
    iIntros ([h1 s1] ns κ κs nt) "(Hh & Hstk & Hsize)".
    iDestruct (stacksize_own_agree with "[$]") as %Heq;subst.
    iMod (stacksize_own_update (S (length s1)) with "[$]") as "[Hsize Hs]".
    iApply fupd_mask_intro;[set_solver|]. iIntros "Hcls".
    iSplit. { iPureIntro. exists CaptureMode. repeat econstructor; eauto. inversion Hscope;subst;auto. }
    iNext. iIntros (rm r0 σ2 efs Hstep) "Hp".
    resolve_next_state. iMod "Hcls". iModIntro.
    rewrite /gen_stack_interp list_to_gmap_stack_push_stack push_stack_length. iFrame.
    rewrite PeanoNat.Nat.add_1_r. by iApply "HΦ".
  Qed.

  Lemma wp_return K K' E n i e v Φ `{!IntoVal (n,e) v} :
    (i <= 0)%Z ->
    Z.abs_nat i <= n ->
    ▷ ([size] (n - (Z.abs_nat i)) -∗
         ⚡={next_state_inv Ω (lifetime_stack (n - (Z.abs_nat i)))}=> ⚡={next_state Ω (lifetime_stack (n - (Z.abs_nat i)))}=>
         WP fill K' (n - (Z.abs_nat i),shift_expr e i) @ E {{ Φ }})
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
    resolve_next_state. iMod "Hcls". rewrite H1.
    iDestruct "Hstate" as "(Hh & Hs & Hsize)".
    iDestruct (gen_stack_interp_stack_pop_inv with "Hs") as "Hs";[eauto|].
    iDestruct (gen_heap_interp_stack_pop_inv _ (lifetime_stack (length s1 - Z.abs_nat i)) with "Hh") as "Hh".
    iMod (stacksize_own_update (length s1 - Z.abs_nat i) with "[$Hsize $Hn]") as "[Hsize Hn]".
    iDestruct (stack_size_auth_inv_intro _ (lifetime_stack (length s1 - Z.abs_nat i)) with "Hsize") as "Hsize".
    iModIntro. iClear "Hp".
    iDestruct ("HΦ" with "Hn") as "Hwp". iFrame.
    iSplitR "Hwp".
    - rewrite <- (@next_state_inv_eq Σ Ω H).
      iModIntro.
      iDestruct (gen_stack_interp_stack_pop with "Hs") as "Hs";[eauto|].
      iDestruct (gen_heap_interp_stack_pop _ (lifetime_stack (length s1 - Z.abs_nat i)) with "Hh") as "Hh".
      iDestruct (stack_size_auth_intro _ (lifetime_stack (length s1 - Z.abs_nat i)) with "Hsize") as "Hsize".
      rewrite <- (@next_state_eq' Σ Ω H).
      iModIntro. iFrame. rewrite popN_stack_length. iFrame.
    - rewrite <- (@next_state_inv_eq Σ Ω H).
      rewrite <- (@next_state_eq' Σ Ω H).
      iModIntro. iModIntro. rewrite /CC_ectxi_language.fill /= fill_proj_eq.
      iFrame.
  Qed.


End lifting.
