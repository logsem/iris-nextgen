From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting weakestpre cl_weakestpre.
From nextgen.case_study Require Export stack_lang stack_transform.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.

From nextgen Require Import nextgen_independent.
From nextgen.lib Require Import invariants.
From nextgen.case_study Require Import rules_unary cl_rules_unary stack_lang_notation.

Set Default Proof Using "Type".
Import uPred.

Lemma fill_inner_cons n e K Ks :
  fill (K :: Ks) (n,e) = fill Ks (n, fill_item K e).
Proof. auto. Qed.
Lemma fill_to_CC_fill K n e :
  CC_ectxi_language.fill K (n,e) = fill K (n,e).
Proof. auto. Qed.

Ltac peel_ctx :=
  try rewrite fill_to_CC_fill; try rewrite fill_inner_cons; simpl fill_item.

Ltac prepare_ctx :=
  (try rewrite /stack_fill_item /=) ;
  let H := fresh "H" in
  match goal with
  | |- context [ WP (?n,?e) @ _ ; ↑ _ ; _ {{ _ }}%I ] =>
      pose proof (construct_ctx_eq n e) as H;try rewrite /= to_of_val in H;
      try rewrite /= construct_ctx_of_val in H;
      try (rewrite H; clear H; simpl app); peel_ctx
  | |- context [ CLWP (?n,?e) @ ↑ _ ; _ {{ _ }}%I ] =>
      pose proof (construct_ctx_eq n e) as H;try rewrite /= to_of_val in H;
      try rewrite /= construct_ctx_of_val in H;
      try (rewrite H; clear H; simpl app); peel_ctx
  end.

Section list_code.
  Open Scope val_scope.

  Definition heap_cons : val :=
    λ: global, <>, "x" "xs" := let: "p" := ⟪"x","xs"⟫ in
                               SOME (href "p").

  Definition heap_map_list : val :=
    rec: global, <>, "map_list", "f" "l" :=
      match: "l" with
        NONE => NONE
      | SOME "p" =>
          let: "hd" := Fst !"p" in
          let: "tl" := Snd !"p" in
          heap_cons ("f" "hd") ("map_list" "f" "tl")
      end.

  Definition empty_list : val := NONEV.
      
End list_code.

Section list_prec.
  Context `{!heapGS Σ Ω}.

  Fixpoint is_heap_list_nat (hd : val) (xs : list nat) : iProp Σ :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ l hd', ⌜hd = SOMEV #(global,l)⌝ ∗ l ↦ ⟪x,hd'⟫ ∗ is_heap_list_nat hd' xs
  end%I.

  Lemma is_heap_list_nat_intro hd xs lft :
    is_heap_list_nat hd xs ⊢ ⚡={Ω <- lft}=> is_heap_list_nat hd xs.
  Proof.
    revert hd. induction xs=>hd.
    - simpl. iIntros "%". iModIntro. auto.
    - simpl.
      iIntros "(%l & %hd' & %Heq & Hl & Hlist)".
      iDestruct (IHxs with "Hlist") as "Hlist".
      iModIntro. iExists _,_. iFrame. auto.
  Qed.

  #[global] Instance is_heap_list_nat_intro' hd xs lft
    : IntoPnextgen _ _ _ := is_heap_list_nat_intro hd xs lft.

  Lemma is_heap_list_nat_ind_intro hd xs lft :
    is_heap_list_nat hd xs ⊢ ⚡◻{ Ω ↑ lft } is_heap_list_nat hd xs.
  Proof.
    apply bnextgen_bounded_ind_GenIndependent_intro.
    simpl. iIntros (c Hc) "HP".
    rewrite -next_state_eq. iModIntro. auto.
  Qed.

  #[global] Instance is_heap_list_nat_ind_intro' hd xs c
    : IntoInextgen Ω c _ _ := is_heap_list_nat_ind_intro hd xs c.

  Lemma is_heap_list_shift hd xs :
    is_heap_list_nat hd xs -∗ ⌜∀ n, shift_val hd n = Some hd⌝.
  Proof.
    iIntros "Hlist" (n).
    destruct xs.
    - simpl. iDestruct "Hlist" as %->. simpl. auto.
    - simpl. iDestruct "Hlist" as "(%l & %hd' & -> & Hl & Hlist)".
      simpl. auto.
  Qed.

  Lemma is_heap_list_permanent hd xs :
    is_heap_list_nat hd xs -∗ ⌜permanent hd⌝.
  Proof.
    iIntros "Hlist".
    destruct xs.
    - simpl. iDestruct "Hlist" as %->. iPureIntro. repeat constructor.
    - simpl. iDestruct "Hlist" as "(%l & %hd' & -> & Hl & Hlist)".
      iPureIntro. repeat constructor.
  Qed.

End list_prec.

Section list_spec.
  Context `{!heapGS Σ Ω}.

  (* TODO: need to repeat the instance declaration for some reason *)
  #[global] Instance heap_stack_ind_intro' l q v n
    : IntoInextgen _ _ _ _ := heap_stack_ind_intro' l q v n.

  Notation "c1 ≤ c2" := (rc locality_lifetime_rel c1 c2) (at level 70).
  
  Lemma heap_list_cons_spec hd xs (n : nat) m c :
    c ≤ (^m) ->
    [size] m ∗ is_heap_list_nat hd xs -∗
    CLWP (m,heap_cons n hd) @ ↑c {{ hd', [size] m ∗ is_heap_list_nat hd'.2 (n :: xs) }}.
  Proof.
    intros Hle.
    assert (∀ lft, GenIndependent CR (λ c : C, build_trans (gT_map (transmap_insert_two_inG
                       (inv_pick_transform c) (C_pick c) Ω))) lft (is_heap_list_nat hd xs)).
    { intros lft. iIntros (c' Hc) "Hlist". rewrite -/(nextgen_omega _ _) -next_state_eq. by iModIntro. }
    iIntros "[Hsize Hlist] /=". prepare_ctx. iApply clwp_bind.
    iApply (clwp_call_global (λ v, ⌜v.2 = _⌝)%I);[auto|eauto|iFrame]. iSplitL;cycle 1.
    { iNext. iIntros "Hsize/=". iApply clwp_value;simpl;eauto. }
    iNext. iModIntro. iIntros (v) "[Hsize %Heq] /=". simpl in Heq. rewrite Heq.
    rewrite /stack_fill_item /=. iDestruct (is_heap_list_shift with "Hlist") as %Hshift.
    iApply (clwp_call_global (λ v, is_heap_list_nat v.2 (n :: xs))%I);
      [rewrite /IntoVal/=/stack_of_val/=;eauto|auto|eauto|iFrame].
    iDestruct (is_heap_list_permanent with "Hlist") as %Hperm.
    iSplitR;cycle 1.
    { iNext. iIntros "Hsize /=".
      iApply clwp_LetIn;[instantiate (1:=(_,⟪#nv n,_⟫%V)); eauto|]. iIntros "!> /=". prepare_ctx.
      iApply clwp_bind.
      iApply clwp_heap_alloc;[instantiate (1:=⟪#nv n,_⟫%V);eauto|repeat constructor;auto|..].
      iIntros "!> %l Hl /=".
      iApply clwp_value. rewrite /stack_fill_item /=.
      iApply clwp_value. simpl. iExists _. iFrame. do 2 (iSplit;[eauto|]).
      iExists l,hd. iFrame. auto. }
    iIntros "!> !> %v' (Hsize & Hlist) /=". iFrame.
  Qed.
  
  Lemma heap_list_map_list_spec (φ : nat -> nat -> Prop) hd xs (f : val) m c :
    c ≤ (^m) ->
    (∀ n, shift_val f n = Some f) -> (* if f is a heap closure, shifting it yields no changes *)
    (∀ x v, expr_subst x v f = f) -> (* f is a closed expression *)
    (⚡◻{ Ω ↑ #∞ } □ ∀ m' c (n : nat), ⌜c ≤ ^m'⌝ -∗ [size] m' -∗ CLWP (m',f (#nv n)) @ ↑c {{ λ v, ∃ n', ⌜v = (m',#nv n')⌝ ∗ ⌜φ n n'⌝ ∗ [size] m' }}) (* ⚡◻{ Ω ↑ #∞ } because f is a heap closure *) -∗
    [size] m -∗
    is_heap_list_nat hd xs -∗
    CLWP (m,heap_map_list f hd) @ ↑c {{ λ hd', ⌜hd'.1 = m⌝ ∗ [size] m ∗ ∃ l, is_heap_list_nat hd'.2 l ∗ ⌜Forall2 (λ n1 n2, φ n1 n2) xs l⌝ }}.
  Proof.
    intros Hle Hshift Hclosed.
    revert m hd Hle. induction xs;intros m hd Hle;iIntros "#Hspec Hsize Hlist".
    - iDestruct "Hlist" as %->. simpl. prepare_ctx.
      iApply clwp_bind.
      iApply (clwp_call_global (λ v, ⌜v.2 = _⌝)%I);[eauto|auto|eauto|iFrame]. iSplitL;cycle 1.
      { iNext. iIntros "Hsize/=". iApply clwp_value;simpl;eauto. }
      iIntros "/= !> !> %v [Hsize ->]". rewrite /stack_fill_item/=.
      iApply (clwp_call_global (λ v, (∃ l, is_heap_list_nat v.2 l ∗ ⌜_ l⌝))%I);[auto|eauto|]. simpl. iFrame. iSplitR.
      { iIntros "!>!> %v [Hsize [%l [Hlist %Hres]]]". iFrame. iSplit;auto. }
      iIntros "!> Hsize /=".
      iApply clwp_case_injl. iIntros "!>/=".
      iApply clwp_value. iExists _. simpl. do 2 (iSplit;[eauto|]). iFrame.
      iExists []. auto.
    - simpl is_heap_list_nat.
      iDestruct "Hlist" as "(%l & %hd' & -> & Hl & Hlist)". prepare_ctx.
      iApply clwp_bind.
      iApply (clwp_call_global (λ v, ⌜v.2 = _⌝)%I);[eauto|auto|eauto|iFrame]. iSplitL;cycle 1.
      { iNext. iIntros "Hsize/=". iApply clwp_value;simpl;eauto. }
      rewrite bnextgen_bounded_ind_weaken_once;[|instantiate (1:=c);repeat constructor].
      iIntros "/= !> !> %v [Hsize ->]". rewrite /stack_fill_item/=.
      iApply (clwp_call_global (λ v, (∃ l, is_heap_list_nat v.2 l ∗ ⌜_ l⌝))%I);[auto|eauto|]. simpl. iFrame. iSplitR.
      { iIntros "!>!> %v [Hsize [%l' [Hlist %Hres]]]". iFrame. auto. }
      iIntros "!> Hsize /=".
      iApply clwp_case_injr. iIntros "!>/=". prepare_ctx.
      iApply clwp_bind.
      iApply clwp_heap_load;[constructor|]. iFrame. iIntros "!> Hl".
      iApply clwp_value;[instantiate (1:=(_,⟪ #nv a, hd' ⟫%V));eauto|simpl]. prepare_ctx.
      iApply clwp_bind. iApply clwp_fst;[eexists (_,_);eauto|]. iIntros "!>/=".
      iApply clwp_value. rewrite /stack_fill_item/=.
      iApply clwp_LetIn. iIntros "!>/=". prepare_ctx.
      iApply clwp_bind.
      iApply clwp_heap_load;[constructor|]. iFrame. iIntros "!> Hl".
      iApply clwp_value;[instantiate (1:=(_,⟪ #nv a, hd' ⟫%V));eauto|simpl]. prepare_ctx.
      iApply clwp_bind. iApply clwp_snd;[instantiate (1:=(_,_));eauto|]. iIntros "!>/=".
      iApply clwp_value;[instantiate (1:=(_,_));eauto|]. rewrite /stack_fill_item/=.
      iApply clwp_LetIn;[instantiate (1:=(_,_));eauto|]. iIntros "!>/=".
      rewrite !Hclosed. prepare_ctx.
      iApply clwp_bind.
      assert (c ≤ (^S m)) as Hle';[etrans;eauto;do 2 constructor;lia|].
      iApply (clwp_wand with "[Hsize]").      
      { rewrite 2!bnextgen_bounded_ind_elim. iApply ("Hspec" with "[%] Hsize"). auto. }
      iIntros "!> %n (%n' & -> & %Hn & Hsize) /=". rewrite /stack_of_val/stack_fill_item/=.
      prepare_ctx. iApply clwp_bind. 
      iApply (clwp_call_global (λ v, ⌜v.2 = _⌝)%I);[auto|eauto|iFrame]. iSplitL;cycle 1.
      { iNext. iIntros "Hsize/=". iApply clwp_value;simpl;eauto. }
      iIntros "/= !> !> %v [Hsize ->]".
      (* inductive call *)
      prepare_ctx. rewrite fill_inner_cons. simpl fill_item. rewrite -/(heap_map_list _ _).
      iApply clwp_bind.
      iApply (clwp_wand with "[Hsize Hlist]").
      { rewrite bnextgen_bounded_ind_elim. iApply (IHxs with "[//] Hsize Hlist"). auto. }
      iIntros "!> %v (%Heq & Hsize & %l' & Hlist & %Hspec) /=". destruct v;simpl in Heq;subst.
      simpl. rewrite /stack_of_val/stack_fill_item/=.
      iDestruct (is_heap_list_shift with "Hlist") as %Hshift'.
      iDestruct (is_heap_list_permanent with "Hlist") as %Hperm'.
      iApply (clwp_call_global (λ v, ⌜shift_val v.2 (-1) = Some v.2⌝ ∗ is_heap_list_nat v.2 (n' :: l'))%I);[eauto|auto|eauto|iFrame].
      iSplitL "Hl";cycle 1.
      { iIntros "!> Hsize". simpl.
        iApply clwp_LetIn;[instantiate (1:=(_,⟪#nv n',_⟫%V)); eauto|]. iIntros "!> /=". prepare_ctx.
        iApply clwp_bind.
        iApply clwp_heap_alloc;[instantiate (1:=⟪#nv n',_⟫%V);eauto|repeat constructor;auto|..].
        iIntros "!> %l2 Hl2 /=".
        iApply clwp_value. rewrite /stack_fill_item /=.
        iApply clwp_value. simpl. iExists _. iFrame. do 3 (iSplit;[eauto|]).
        iExists l2,v. iFrame. auto. }
      iIntros "!> !> %v' (Hsize & %Hshift2 & Hlist)". iExists _. iFrame. do 2 (iSplit;[eauto|]).
      iExists (n' :: l'). iFrame. iPureIntro. apply Forall2_cons. split;auto.
  Qed.
    
End list_spec.
