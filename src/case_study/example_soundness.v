From nextgen Require Import examples.
From nextgen.lib Require Import wsat fancy_updates.
From nextgen Require Import nextgen_soundness.
From nextgen.case_study.program_logic Require Import adequacy gen_heap_lifting.
From nextgen.case_study Require Import stack_lang rules_unary.
From iris.proofmode Require Import proofmode.

Class stacksizePreGS (Σ : gFunctors) (Ω : gTransformations Σ) := StackSizePreGS {
  heapG_excl_nat_stacksizePreGS :: genIndInG Σ Ω (excl_authUR natR)
                                                                   }.

Class heapPreGS (Σ : gFunctors) (Ω : gTransformations Σ) := HeapPreGS {
  heap_preG_invGS :: invGIndpreS Σ Ω;
  heap_preG_heap  :: gen_heapIndGpreS loc val Σ Ω;
  heap_preG_stack :: gen_heapNoGpreS (nat * loc) val Σ Ω;
  heap_preG_size  :: stacksizePreGS Σ Ω
}.

Lemma stacksize_init `{!stacksizePreGS Σ Ω} (n : nat) :
  ⊢ |==> ∃ H : stacksizeGS Σ Ω, 
      @own Σ _ (H.(heapG_excl_nat_stacksizeGS)).(genInG_inG) H.(heapG_stacksize_name) (excl_auth_auth n) ∗
      @own Σ _ (H.(heapG_excl_nat_stacksizeGS)).(genInG_inG) H.(heapG_stacksize_name) (excl_auth_frag n).
              (* [size] n. *)
Proof.
  iMod own_alloc as (γ) "HH".
  { apply @excl_auth_valid with (a:=n). }
  iDestruct "HH" as "[H1 H2]".
  iExists (StackSizeGS Σ Ω γ _).
  iFrame. simpl. iFrame. done.
Qed.

Definition initial_cfg : cfg lang := ([(0,example1)], (∅,[])).

Theorem soundness_example1 Σ Ω `{heapPreGS Σ Ω} :
  ∀ v2 σ2, rtc erased_step initial_cfg ([stack_of_val v2], σ2) → v2.2 = NatV 42.
Proof.
  intros v2 σ2 Hsteps.
  cut (adequate_single_thread NotStuck ((0,example1) : stack_expr) (∅,[]) (λ v _, v.2 = NatV 42)).
  { intros Hadequate. inversion Hadequate. apply adequate_result in Hsteps. auto. }
  eapply (@wp_adequacy_no_lc_single_thread Σ Ω _ (heap_preG_stack.(gen_heapNoGpreS_heap)).(ghost_map_inNoG)
            lang heap_preG_invGS next_state_f (next_state_f_cmra_morphism Σ Ω) NotStuck).
  intros Hinv κs. simpl.
  iMod (gen_heap_init_ind (∅ : gmap loc val)) as (Hheap) "[Hh _]".
  iMod (gen_heap_init_no_names (∅ : gmap (nat * loc) val)) as (γs1 γs2) "[Hs _]".
  iMod (stacksize_init 0) as (Hsize) "[Hsize Hfrag]".
  set (Hstack := GenHeapNoGS _ _ Σ Ω γs1 γs2).
  set (heapGΣ := (HeapGS Σ Ω Hinv Hheap Hstack Hsize)).
  iExists (λ σ _, let '(h,s) := σ in
                  (@gen_heap_interp _ _ _ _ _ (into_gen_heap_from_ind Hheap) h
                     ∗ @gen_stack_interp _ _ heapGΣ s
                     ∗ @own _ _ (Hsize.(heapG_excl_nat_stacksizeGS)).(genInG_inG) Hsize.(heapG_stacksize_name)
                                                                                          (excl_auth_auth (length s)))%I).
  iExists (λ _, True%I).
  iDestruct "Hs" as (m Hdom) "[Hs _]". simpl.
  iModIntro. iFrame. iApply (@example1_spec Σ Ω heapGΣ with "Hfrag []");auto.
Qed.
