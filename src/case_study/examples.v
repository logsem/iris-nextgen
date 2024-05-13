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

Ltac peel_ctx := rewrite fill_inner_cons;simpl fill_item.

Ltac prepare_ctx :=
  (try rewrite /stack_fill_item /=) ;match goal with
  | |- context [ WP (?n,?e) @ _ ; _ {{ _ }}%I ] =>
      rewrite (construct_ctx_eq n e);simpl app;
      peel_ctx
  end.

Section examples.
  Open Scope expr_scope.

  Definition example1 : expr :=
    (λ: global, "k", "y" := let: "x" := sref 42 in !"x") ().

  Definition example2 : expr :=
    (λ: global, "<>", "f" := let: "y" := sref 42 in "f" ("y")) (λ: global, "<>", "x" := !"x").

  Definition example3 : expr :=
    let: "g" := λ: global, "<>", "f'" := "f'" () in
    let: "f" := λ: global, "<>", "<>" := let: "x" := sref 42 in "g" (λ: local 0, "<>", "<>" := !"x") in
    "f" ().
  
  Definition stuck_example : expr :=
    ! ((λ: global, "<>", "<>" := sref 42) ()).

  Definition example4 g : expr :=
    let: "f" := λ: global, "k", "g" := let: "x" := sref 42 in "g" ⟪"x","k"⟫ ;; !"x" in
    "f" g.

End examples.

Section stack_lang_examples.
  Context `{heapGS Σ}.

  Lemma example1_spec :
    {{{ [size] 0 }}} (0,example1) @ ↑^0 {{{ v, RET v; ⌜v.2 = NatV 42⌝ }}}.
  Proof.
    iIntros (Φ) "Hsize HΦ /=". rewrite /example1. prepare_ctx.
    iApply wp_call_global;[eauto|iFrame]. iNext. iIntros "Hsize /=". prepare_ctx.
    iApply wp_stack_alloc;[repeat constructor|iFrame].
    iNext. iIntros (l) "[Hsize Hl]". peel_ctx.
    iApply wp_LetIn. iIntros "!>". simpl subst'.
    iApply (wp_stack_load);[|iFrame];[eauto|].
    iNext. iIntros "[Hsize Hl]". peel_ctx.
    iApply wp_return;[|eauto|lia|iFrame].
    { apply rc_l. }
    iNext. iIntros "Hsize". iClear "Hl".
    iModIntro.
    simpl. iApply wp_value. iApply "HΦ". simpl. auto.
  Qed.

  Lemma example2_spec :
    {{{ [size] 0 }}} (0,example2) @ ↑^0 {{{ v, RET v; ⌜v.2 = NatV 42⌝ }}}.
  Proof.
    iIntros (Φ) "Hsize #HΦ /=". rewrite /example2. prepare_ctx.
    iApply wp_call_global;[eauto|iFrame]. iIntros "!>". iIntros "Hsize /=". prepare_ctx.
    iApply wp_stack_alloc;[repeat constructor|iFrame].
    iNext. iIntros (l) "[Hsize Hl]". peel_ctx.
    iApply wp_LetIn. iIntros "!>". simpl subst'.
    iApply wp_call_global;[eauto|iFrame]. iNext. iIntros "Hsize /=".
    prepare_ctx.
    iApply wp_stack_load;[|iFrame];eauto.
    iNext. iIntros "[Hsize Hl]". peel_ctx.
    iApply wp_return;[|eauto|lia|iFrame];[do 2 constructor;lia|].
    iNext. iIntros "Hsize /=".
    iDestruct (stack_stack_pop_intro with "Hl") as "Hl";[eauto|].
    iModIntro. prepare_ctx.
    iApply wp_return;[|eauto|lia..|iFrame];[apply rc_l|]. iNext. iClear "Hl".
    iIntros "Hsize /=". iClear "Hsize". iModIntro.
    iApply wp_value. iApply "HΦ";auto.
  Qed.

  Lemma example3_spec :
    {{{ [size] 0 }}} (0,example3) @ ↑^0 {{{ v, RET v; ⌜v.2 = NatV 42⌝ }}}.
  Proof.
    iIntros (Φ) "Hsize #HΦ /=". rewrite /example2. prepare_ctx.
    iApply wp_LetIn. iIntros "!>". simpl subst'.
    iApply wp_LetIn. iIntros "!>". simpl subst'.
    iApply wp_call_global;[eauto|iFrame]. iNext. iIntros "Hsize /=". prepare_ctx.
    iApply wp_stack_alloc;[repeat constructor|iFrame]. iNext. iIntros (l) "[Hsize Hl]". peel_ctx.
    iApply wp_LetIn. iIntros "!>". simpl subst'.
    iApply wp_call_global;[eauto|iFrame]. iNext. iIntros "Hsize /=". prepare_ctx.
    iApply wp_call_local;[eauto..|iFrame]. simpl. prepare_ctx.
    iNext. iIntros "Hsize".
    (* NOTE: the local stack pointer has been shifted to point two frame down *)
    iApply wp_stack_load;[|iFrame];eauto. iNext. iIntros "[Hsize Hl]". peel_ctx.
    iApply wp_return;[do 2 constructor;lia|eauto|lia|]. iFrame. iNext.
    iIntros "Hsize /=".
    iDestruct (stack_stack_pop_intro _ _ _ _ 2 with "Hl") as "Hl";[lia|].
    iModIntro. prepare_ctx.
    iApply wp_return;[do 2 constructor;lia|eauto|lia|]. iFrame. iNext. iIntros "Hsize /=".
    iDestruct (stack_stack_pop_intro _ _ _ _ 1 with "Hl") as "Hl";[lia|].
    iModIntro. prepare_ctx.
    iApply wp_return;[do 2 constructor;lia|eauto|lia..|]. iFrame. iNext. iIntros "Hsize /=".
    iClear "Hl".
    iModIntro. iApply wp_value. iApply "HΦ";auto.
  Qed.
  
  (* The following lemma cannot be proved, since the program will get
  stuck once the caller tried to load the callee's now popped stack
  location *)
  Lemma stuck_example_failed_spec :
    {{{ [size] 1 }}} (1,stuck_example) @ ↑^0 {{{ v, RET v; False }}}.
  Proof.
    iIntros (Φ) "Hsize #HΦ /=". rewrite /stuck_example. prepare_ctx.
    iApply wp_call_global;[eauto|iFrame]. iNext. iIntros "Hsize /=". prepare_ctx.
    iApply wp_stack_alloc;[repeat constructor|iFrame]. iNext. iIntros (l) "[Hsize Hl]". peel_ctx.
    (* STUCK! the points-to for l gets lost, its lifetime is not less than 1 *)
  Abort.

  Definition logN : namespace := nroot .@ "logN".

  Local Definition inv : namespace -> locality_lifetime -> iProp Σ -> iProp Σ := inv.
  
  Lemma example4_spec (e : expr) :
    (forall v, expr_subst "f" v e = e) -> (* e does not contain free f *)
    (∀ (j k : nat) v1 v2 K', ⌜k <= j⌝ →
                      {{{ [size] j
                      ∗ (∃ (i : nat) K (off : nat), ⌜(off ≤ j)⌝ ∧ ⌜shift_expr v2 (-1) = Some (Cont off K)⌝ ∧ ⌜(i = j - off)⌝ ∧
                                      (∀ v', (∃ n, ⌜v' = Nat n⌝) → [size] i -∗
                                      ⚡={Ω <- (lifetime_stack i)}=> WP fill K (i,v') @ ↑^i {{ λ v, ∃ n, ⌜v.2 = NatV n⌝ }}))
                      ∗ (∃ i l (off : nat), ⌜(off <= j)⌝ ∧ ⌜shift_expr v1 1 = Some (Loc (local off) l)⌝ ∧ ⌜(i = j - (Z.abs_nat off))⌝ ∧
                                      inv (logN .@ l) (^S i) (∃ v, i @@ l ↦ v ∗ ∃ m, ⌜v = NatV m⌝))
                      ∗ (∀ v', (∃ n, ⌜v' = Nat n⌝) → [size] j -∗
                        ⚡={Ω <- (lifetime_stack j)}=> WP fill K' (j,v') @ ↑^k {{ λ v, ∃ n, ⌜v.2 = NatV n⌝ }}) }}}
                  fill K' ((j, (λ: global, "k", "x" := e) ⟪ v1, v2 ⟫)) @ ↑^k
                  {{{ v, RET v; ∃ n, ⌜v.2 = NatV n⌝ }}}) ⊢
    {{{ [size] 0 }}} (0,example4 (λ: global, "k", "x" := e)) @ ↑^0 {{{ v, RET v; ∃ n, ⌜v.2 = NatV n⌝ }}}.
  Proof.
    iIntros (Hfree) "#Hadv_spec".
    iModIntro. iIntros (Φ) "Hsize #HΦ /=". rewrite /example4. prepare_ctx.
    iApply wp_LetIn. iIntros "!>". simpl subst'.
    iApply wp_call_global;[eauto|iFrame]. iIntros "!> Hsize". prepare_ctx.
    iApply wp_stack_alloc;[repeat constructor|iFrame]. iIntros "!>" (l) "[Hsize Hl] /=". prepare_ctx.
    iApply wp_LetIn. iIntros "!> /=".
    prepare_ctx. rewrite Hfree. iApply fupd_wp.
    iMod (@inv_alloc _ _ _ _ locality_lifetime_pick _ (logN .@ l) _
            (lifetime_stack 1) (∃ v, 0 @@ l ↦ v ∗ ∃ m, ⌜v = NatV m⌝) with "[Hl]") as "#Hinv".
    { apply bnextgen_bounded_ind_GenIndependent_intro.
      intros c' Hle. iIntros "(%v & Hl & (%m & ->))".
      inversion Hle;subst.
      - inversion H0;subst.
        iDestruct (stack_stack_pop_intro _ _ _ _ f2 with "Hl") as "Hl";[lia|].
        rewrite -next_state_eq. iModIntro. eauto.
      - iDestruct (stack_stack_pop_intro _ _ _ _ 1 with "Hl") as "Hl";[lia|].
          rewrite -next_state_eq. iModIntro. eauto. }
    { eauto. }
    iApply ("Hadv_spec" with "[] [-] [//]");[iPureIntro;lia|]. iFrame.
    iSplitR;[|iSplitR].
    - (* the unknown function returns to the first caller *)
      iExists 1,[],0.
      iSplit;[iPureIntro;lia|].
      iSplit;[auto|].
      iSplit;[iPureIntro;lia|].
      iIntros (v' Hv') "Hsize".
      iClear "Hinv Hadv_spec". iModIntro.
      destruct Hv' as [? ->]. simpl. iApply wp_value;eauto.
    - (* invariant for the stack variable parameter *)
      iExists 0,l,1.
      iSplit;[iPureIntro;lia|].
      iSplit;[auto|].
      iSplit;[iPureIntro;lia|].
      iFrame "Hinv".
    - (* the unknown function returns normally to the caller *)
      iIntros (v' [? ->]) "Hsize".
      iDestruct (next_state_stack_inv_intro _ _ 1 with "Hinv") as "Hinv'";[lia|].
      iClear "Hinv Hadv_spec". iRename "Hinv'" into "Hinv".
      iModIntro. iSimpl.  prepare_ctx.
      iApply wp_LetIn. iNext. iSimpl. prepare_ctx.
      iApply (wp_atomic_under_ectx _ (⊤ ∖ ↑logN.@l));eauto.
      { apply is_atomic_correct;eauto. }
      { apply is_atomic_sub_values;eauto. }
      { apply is_atomic_normal;eauto. }
      { unfold SameGeneration. by cbn. }
      iMod (inv_acc with "Hinv") as "[>Hl Hcls]";[set_solver|].
      iDestruct "Hl" as (v) "[Hl %Heq]". destruct Heq as [? ->].
      iModIntro. prepare_ctx. iApply wp_stack_load;[|iFrame];eauto.
      iFrame. iIntros "!> [Hsize Hl] /=".
      iApply wp_value. iMod ("Hcls" with "[Hl]") as "_";[eauto|].
      iModIntro. prepare_ctx.
      iApply wp_return;[apply rc_l|eauto|lia|]. iFrame.
      iIntros "!> Hsize". iClear "Hinv". iModIntro.
      simpl. iApply wp_value. eauto.
  Qed.
      
End stack_lang_examples.


