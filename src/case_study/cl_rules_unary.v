From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting
     CC_ectxi_language CC_ectx_lifting weakestpre gen_heap_lifting cl_weakestpre.
From nextgen.case_study Require Export stack_lang stack_transform.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From nextgen Require Import nextgen_basic gen_trans gmap_view_transformation nextgen_id.
From stdpp Require Import binders.
Set Default Proof Using "Type".
Import uPred.

From nextgen Require Export rules_unary.

Section lifting.
  Context `{heapGS Σ}.

  (* typeclass instances for next state independence modality *)
  #[global] Instance stack_size_frag_ind_intro' s n
    : IntoInextgen _ _ _ _ := stack_size_frag_ind_intro s n.
  #[global] Instance heap_stack_ind_intro' (l : loc) (q : dfrac) (v : val) n
    : IntoInextgen _ _ _ _ := heap_stack_ind_intro l q v n.
  #[global] Instance heap_inv_ind_intro c N P
    : IntoInextgen _ _ _ _ := next_state_heap_inv_ind_intro c N P.
  
  #[global] Instance later_credits_ind_intro' m n
    : IntoInextgen _ _ _ _ := later_credits_ind_intro m n.

  Lemma clwp_LetIn c E e1 e2 v1 x Φ (n : nat) `{!IntoVal (n,e1) v1} :
    ▷ (CLWP (n,subst' x v1.2 e2) @ ↑c; E {{ Φ }}) ⊢ CLWP (n,LetIn x e1 e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_LetIn;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_bin_op c E op e1 e2 n v1 v2 w Φ `{!IntoVal (n,e1) (n,v1), !IntoVal (n,e2) (n,v2)} :
    binop_eval op v1 v2 = Some w →
    ▷ (CLWP (n, of_val w) @ ↑c; E {{ Φ }})
      ⊢ CLWP (n, BinOp op e1 e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (?) "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_bin_op;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_if_true c E e1 e2 n Φ :
    ▷ (CLWP (n,e1) @ ↑c; E {{ Φ }}) ⊢ CLWP (n,If (#♭ true) e1 e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_if_true;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_if_false c E e1 e2 n Φ :
    ▷ (CLWP (n,e2) @ ↑c; E {{ Φ }}) ⊢ CLWP (n, If (#♭ false) e1 e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_if_false;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_case_injl c E e x v e1 e2 n m Φ `{!IntoVal (n,e) (m,InjLV v)} :
    ▷ (CLWP (n,subst' x v e1) @ ↑c; E {{ Φ }}) ⊢ CLWP (n,Case e x e1 e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_case_injl;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_case_injr c E e x v e1 e2 n m Φ `{!IntoVal (n,e) (m,InjRV v)} :
    ▷ (CLWP (n,subst' x v e2) @ ↑c; E {{ Φ }}) ⊢ CLWP (n,Case e x e1 e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_case_injr;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_fst c E e1 e2 v1 n Φ `{!IntoVal (n,e1) v1, !AsVal (n,e2)} :
    ▷ (CLWP (n,e1) @ ↑c; E {{ Φ }})
      ⊢ CLWP (n,Fst (Pair e1 e2)) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_fst;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_snd c E e1 e2 n v2 Φ `{!AsVal (n,e1), !IntoVal (n,e2) v2} :
    ▷ (CLWP (n,e2) @ ↑c; E {{ Φ }})
      ⊢ CLWP (n, Snd (Pair e1 e2)) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_snd;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_mask c E l n Φ :
    ▷ (CLWP (n,Loc borrow l) @ ↑c; E {{ Φ }})
      ⊢ CLWP (n, Mask (Loc global l)) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_mask;eauto;iNext;by iApply "H".
  Qed.

  Lemma clwp_stack_alloc c E n e v Φ `{!IntoVal (n,e) (n,v)} :
    0 < n -> (* stack is non empty *)
    ▷ (∀ l, [size] n ∗ (n - 1) @@ l ↦ v -∗ CLWP (n,Loc (local 0) l) @ ↑c; E {{ Φ }})
      ∗ ▷ [size] n
      ⊢ CLWP (n,Salloc e) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (?) "[H1 H2]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_stack_alloc; eauto. iFrame. iNext. iIntros (l) "Hl".
    iSpecialize ("H1" with "Hl"). rewrite !unfold_clwp.
    by iApply "H1".
  Qed.

  Lemma clwp_heap_alloc c E n e v Φ `{!IntoVal (n,e) (n,v)} :
    permanent v ->
    ▷ (∀ l, l ↦ v -∗ CLWP (n,Loc global l) @ ↑c; E {{ Φ }})
      ⊢ CLWP (n,Halloc e) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (?) "H1"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_heap_alloc; eauto. iFrame. iNext. iIntros (l) "Hl".
    iSpecialize ("H1" with "Hl"). rewrite !unfold_clwp.
    by iApply "H1".
  Qed.

  Lemma clwp_heap_load c E l δ n v Φ :
    heap_tag δ ->
    ▷ (l ↦ v -∗ CLWP (n,of_val v) @ ↑c; E {{ Φ }})
      ∗ ▷ l ↦ v
      ⊢ CLWP (n,Load (Loc δ l)) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (?) "[H1 H2]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_heap_load; eauto. iFrame. iNext. iIntros "Hl".
    iSpecialize ("H1" with "Hl").
    by iApply "H1".
  Qed.

  Lemma clwp_stack_load c E l (j : nat) v v' n Φ :
    shift_val v j = Some v' ->
    ▷ ([size] n ∗ (n - 1 - Z.abs_nat j) @@ l ↦ v -∗ CLWP (n,of_val v') @ ↑c; E {{ Φ }})
      ∗ ▷ (n - 1 - Z.abs_nat j) @@ l ↦ v
      ∗ ▷ [size] n
      ⊢ CLWP (n,Load (Loc (local j) l)) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (?) "[H1 H2]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_stack_load; eauto. iFrame. iNext. iIntros "Hl".
    iSpecialize ("H1" with "Hl").
    by iApply "H1".
  Qed.

  Lemma clwp_heap_store c E e l δ v Φ `{!IntoVal (n,e) (n,v)} :
    permanent v ->
    heap_tag δ ->
    ▷ (l ↦ v -∗ CLWP (n,lang.Unit) @ ↑c; E {{ Φ }})
      ∗ ▷ l ↦ -
      ⊢ CLWP (n,Store (Loc δ l) e) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (? ?) "[H1 H2]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_heap_store; eauto. iFrame. iNext. iIntros "Hl".
    iSpecialize ("H1" with "Hl").
    by iApply "H1".
  Qed.

  Lemma clwp_stack_store c E e l (j : nat) v v' w Φ `{!IntoVal (n,e) (n,v)} :
    shift_val v (-j) = Some v' ->
    ▷ ([size] n ∗ (n - 1 - j) @@ l ↦ v' -∗ CLWP (n,lang.Unit) @ ↑c; E {{ Φ }})
      ∗ ▷ (n - 1 - j) @@ l ↦ w
      ∗ ▷ [size] n
      ⊢ CLWP (n,Store (Loc (local j) l) e) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (?) "[H1 H2]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_stack_store; eauto. iFrame. iNext. iIntros "Hl".
    iSpecialize ("H1" with "Hl").
    by iApply "H1".
  Qed.

  Lemma clwp_bind K c E e Φ :
  CLWP e @ ↑c; E {{ v, CLWP fill K (stack_of_val v) @ ↑c; E {{ Φ }} }}
                 ⊢ CLWP fill K e @ ↑c; E {{ Φ }}.
  Proof. by iApply clwp_bind. Qed.

  Local Lemma fill_inner_cons n e K Ks :
    fill (K :: Ks) (n,e) = fill Ks (n, fill_item K e).
  Proof. auto. Qed.
                                       
  Lemma clwp_call_global Φ' E n c f x e1 e2 v2' v2 Φ `{!IntoVal (n,e2) (n,v2)} `{Hindep:!∀ v, GenIndependent2Ω Ω c (Φ' v)} :
    c ≤ (^n) ->
    shift_val v2 (1) = Some v2' ->
    ▷ (⚡◻{Ω ↑ c} ∀ v, [size] n ∗ Φ' (n, v) -∗ Φ (n, v)) ∗
    ▷ ([size] S n -∗ CLWP (S n,(subst' f (RecV global BAnon f x e1) (subst' x v2' e1)))
                     @ ↑c; E {{ λ v, ∃ v', ⌜v.1 = S n⌝ ∗ ⌜shift_val v.2 (- 1%nat) = Some v'⌝ ∗ [size] v.1 ∗ Φ' (n, v') }})
      ∗ ▷ [size] n
      ⊢ CLWP (n,Call (Rec global BAnon f x e1) e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (Hc ?) "[Hwand [H1 H2]]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_call_global; eauto. iFrame. iNext. iIntros "Hl". simpl.
    eassert (CC_ectxi_language.fill _ (_,_) = fill _ (_,_)) as ->;[eauto|].
    rewrite -/(fill_item (ReturnRCtx (ContV 1 K)) _ ).
    rewrite -fill_inner_cons.
    iSpecialize ("H1" with "Hl").
    iApply ("H1" with "[-]").
    iDestruct (bnextgen_bounded_ind_sep with "[$Hwand $HK]") as "HK".
    rewrite bnextgen_bounded_ind_idemp.
    iApply (bnextgen_ind_mono with "HK");iIntros "HK".
    iIntros ([m v]) "[%v' [%Heq [%Hshift [Hsize Hϕ]]]]". simpl in Heq. subst m.
    rewrite /= /stack_fill_item /=.
    iApply (wp_return);[|replace (S n - 1) with n by lia;eauto|eauto|lia|].
    { instantiate (1:=(_,_));eauto. }
    { rewrite -shift_of_val Hshift/=//. }
    iFrame. iIntros "!> Hs".
    replace (S n - 1) with n by lia.
    iDestruct (gen_ind_insert2_intro with "Hϕ") as "Hϕ";[eauto..|].
    (* iDestruct (bnextgen_bounded_ind_bnextgen_intro with "Hϕ") as "Hϕ";[eauto|]. *)
    iDestruct (bnextgen_bounded_ind_bnextgen_intro with "HK") as "HK";[eauto|].
    rewrite -!next_state_eq'.
    iModIntro.
    rewrite !bnextgen_bounded_ind_elim.
    iDestruct "HK" as "[Hwand HK]".
    iSpecialize ("HK" $! (_,_)). iApply "HK". iApply "Hwand". iFrame.
  Qed.

  Lemma clwp_call_local Φ' E n c (i : nat) f x e1 e2 e1' v2' v2 Φ `{!IntoVal (n,e2) (n,v2)} `{Hindep:!∀ v, GenIndependent2Ω Ω c (Φ' v)} :
    c ≤ (^n) ->
    shift_expr e1 (i + 1) = Some e1' ->
    shift_val v2 (1) = Some v2' ->
    ▷ (⚡◻{Ω ↑ c} ∀ v, [size] n ∗ Φ' (n, v) -∗ Φ (n, v)) ∗
    ▷ ([size] S n -∗ CLWP (S n,(subst' f (RecV (local i) BAnon f x e1) (subst' x v2' e1')))
                     @ ↑c; E {{ λ v, ∃ v', ⌜v.1 = S n⌝ ∗ ⌜shift_val v.2 (- 1%nat) = Some v'⌝ ∗ [size] v.1 ∗ Φ' (n, v') }})
      ∗ ▷ [size] n
      ⊢ CLWP (n,Call (Rec (local i) BAnon f x e1) e2) @ ↑c; E {{ Φ }}.
  Proof.
    iIntros (Hc ? ?) "[Hwand [H1 H2]]"; rewrite !unfold_clwp; iIntros (K Ψ) "HK"; simpl in *.
    iApply wp_call_local; eauto. iFrame. iNext. iIntros "Hl". simpl.
    eassert (CC_ectxi_language.fill _ (_,_) = fill _ (_,_)) as ->;[eauto|].
    rewrite -/(fill_item (ReturnRCtx (ContV 1 K)) _ ).
    rewrite -fill_inner_cons.
    iSpecialize ("H1" with "Hl").
    iApply "H1".
    iModIntro.
    iIntros ([m v]) "[%v' [%Heq [%Hshift [Hsize Hϕ]]]]". simpl in Heq. subst m.
    rewrite /= /stack_fill_item /=.
    iApply (wp_return);[|replace (S n - 1) with n by lia;eauto|eauto|lia|].
    { instantiate (1:=(_,_));eauto. }
    { rewrite -shift_of_val Hshift/=//. }
    iFrame. iIntros "!> Hs".
    replace (S n - 1) with n by lia.
    iDestruct (gen_ind_insert2_intro with "Hϕ") as "Hϕ";[eauto..|].
    (* iDestruct (bnextgen_bounded_ind_bnextgen_intro with "Hϕ") as "Hϕ";[eauto|]. *)
    iDestruct (bnextgen_bounded_ind_bnextgen_intro with "HK") as "HK";[eauto|].
    iDestruct (bnextgen_bounded_ind_bnextgen_intro with "Hwand") as "Hwand";[eauto|].
    rewrite -!next_state_eq'.
    iModIntro.
    rewrite !bnextgen_bounded_ind_elim.
    iSpecialize ("HK" $! (_,_)). iApply "HK". iApply "Hwand". iFrame.
  Qed.

End lifting.
