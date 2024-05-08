From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting weakestpre.
From nextgen.case_study Require Export stack_lang stack_transform.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.

From nextgen Require Import nextgen_independent.
From nextgen.lib Require Import invariants.
From nextgen.case_study Require Import rules_unary stack_lang_notation.

Set Default Proof Using "Type".
Import uPred.

Lemma fill_inner_cons n e K Ks :
  fill (K :: Ks) (n,e) = fill Ks (n, fill_item K e).
Proof. auto. Qed.
Lemma fill_to_CC_fill K n e :
  CC_ectxi_language.fill K (n,e) = fill K (n,e).
Proof. auto. Qed.

Ltac peel_ctx :=
  try rewrite fill_to_CC_fill; rewrite fill_inner_cons; simpl fill_item.

Ltac prepare_ctx :=
  (try rewrite /stack_fill_item /=) ;
  let H := fresh "H" in
  match goal with
  | |- context [ WP (?n,?e) @ _ ; ↑ _ ; _ {{ _ }}%I ] =>
      pose proof (construct_ctx_eq n e) as H;try rewrite /= to_of_val in H;
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
          heap_cons ("f" "hd") ("map_list" "tl")
      end.

  Definition stack_cons : val :=
    λ: global, <>, "x" "xs" := let: "p" := ⟪"x","xs"⟫ in
                               SOME (sref "p").

  Definition stack_map_list : val :=
    rec: global, <>, "map_list", "f" "l" :=
      match: "l" with
        NONE => NONE
      | SOME "p" =>
          let: "hd" := Fst !"p" in
          let: "tl" := Snd !"p" in
          stack_cons ("f" "hd") ("map_list" "tl")
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

  Fixpoint is_stack_list_nat (i : nat) (hd : val) (xs : list nat) : iProp Σ :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ l hd' j, ⌜hd = SOMEV #(global,l)⌝ ∗ ⌜j <= i⌝ ∗ j @@ l ↦ ⟪x,hd'⟫ ∗ is_stack_list_nat i hd' xs
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

  Lemma is_stack_list_nat_intro i hd xs j :
    i < j ->
    is_stack_list_nat i hd xs ⊢ ⚡={Ω <- ^j}=> is_stack_list_nat i hd xs.
  Proof.
    intros Hlt.
    revert hd. induction xs=>hd.
    - simpl. iIntros "%". iModIntro. auto.
    - simpl.
      iIntros "(%l & %hd' & %i' & %Heq & %Hle & Hl & Hlist)".
      iDestruct (IHxs with "Hlist") as "Hlist".
      iDestruct (stack_stack_pop_intro _ _ _ _ j with "Hl") as "Hl";[lia|].
      iModIntro. iExists _,_,_. iFrame. auto.
  Qed.

  Lemma is_stack_list_nat_weaken i i' hd xs :
    i <= i' ->
    is_stack_list_nat i hd xs ⊢ is_stack_list_nat i' hd xs.
  Proof.
    revert hd. induction xs=>hd.
    - simpl. auto.
    - simpl.
      iIntros (Hle) "(%l & %hd' & %j & %Heq & %Hj & Hl & Hlist)".
      iDestruct (IHxs with "Hlist") as "Hlist";auto.
      iExists _,_,_. iFrame. iSplit;auto.
      iPureIntro. lia.
  Qed.

  #[global] Instance is_heap_list_nat_intro' hd xs lft
    : IntoPnextgen _ _ _ := is_heap_list_nat_intro hd xs lft.
  
End list_prec.

Section list_spec.
  Context `{!heapGS Σ Ω}.
  
  Lemma heap_list_cons_spec hd xs (n : nat) m :
    {{{ [size] m ∗ is_heap_list_nat hd xs }}}
      (m,heap_cons n hd) @ ↑^m
    {{{ hd', RET hd'; [size] m ∗ is_heap_list_nat hd'.2 (n :: xs) }}}.
  Proof.
    iIntros (Φ) "[Hsize Hlist] #HΦ /=". prepare_ctx.
    iApply wp_call_global;[eauto|iFrame]. iIntros "!> Hsize /=". prepare_ctx.
    iApply wp_return;[replace (S m - 1) with m by lia;apply rc_l|auto|lia|iFrame].
    iIntros "!> Hsize /=". replace (m - 0) with m by lia. iModIntro. rewrite /stack_fill_item /=.
    eassert (fill [] _ = _) as <-;eauto.
    iDestruct (is_heap_list_shift with "Hlist") as %Hshift.
    iApply wp_call_global;[eauto|eauto|iFrame]. iIntros "!> Hsize /=". prepare_ctx.
    iApply wp_LetIn;[|iIntros "!> /=";simpl subst'].
    { instantiate (1:=(_,⟪#nv n,_⟫%V)). rewrite /IntoVal/=/stack_of_val. f_equal;eauto. }
    prepare_ctx. iDestruct (is_heap_list_permanent with "Hlist") as %Hpermanent.
    iApply wp_heap_alloc.
    { instantiate (1:=⟪#nv n,_⟫%V). rewrite /IntoVal/=/stack_of_val. f_equal;eauto. }
    { constructor;auto. constructor. }
    iIntros "!> %l Hl /=". prepare_ctx.
    iApply wp_return;[replace (S m - 1) with m by lia;apply rc_l|auto|lia|iFrame].
    iIntros "!> Hsize". iModIntro. simpl. replace (m - 0) with m by lia.
    iApply wp_value. simpl.
    iApply "HΦ". iFrame. iExists l,hd.
    simpl. iFrame. auto.
  Qed.

    
End list_spec.
