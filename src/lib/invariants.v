From stdpp Require Export namespaces.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import proofmode.
From nextgen.lib Require Import wsat.
From nextgen.lib Require Export fancy_updates.
From nextgen Require Import nextgen_pointwise.
From iris.prelude Require Import options.
Import uPred.
Import le_upd_if.


(** In the base logic of Iris, invariants are defined semantically,
    while the internal model of invariants is abstracted away.

    In this version, we expose the true definition of invariants, to
    allow for easy proof of a nextgen introduction.  Alternatively,
    one needs to express the introduction of a transformation into Ω
*)

(** ** Semantic definition of invariants (do not survive a nextgen) *)
Local Definition inv_def `{!invGIndS_gen hlc Σ Ω A pick} (N : namespace) (c : C) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → (* ∀ c', ⌜CR c c'⌝ →  *)
    (* ⚡={transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω}=> *)
    |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
Definition inv_sem := inv_aux.(unseal).
Global Arguments inv_sem {hlc Σ Ω A pick _} N c P.
Local Definition inv_sem_unseal : @inv_sem = @inv_def := inv_aux.(seal_eq).
Global Instance: Params (@inv_sem) 4 := {}.

(** ** Internal model of invariants *)
Local Definition own_inv `{!invGIndS_gen hlc Σ Ω A pick} (N : namespace) (c : C) (P : iProp Σ) : iProp Σ :=
  ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ ownI i P ∧ ownC i c.
Local Definition own_inv_aux : seal (@own_inv). Proof. by eexists. Qed.
Definition inv := own_inv_aux.(unseal).
Global Arguments inv {hlc Σ Ω A pick _} N c P.
Local Definition inv_unseal : @inv = @own_inv := own_inv_aux.(seal_eq).
Global Instance: Params (@inv) 4 := {}.

(** * Invariants *)
Section inv.
  Context `{!invGIndS_gen hlc Σ Ω A pick}.
  Implicit Types i : positive.
  Implicit Types N : namespace.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.

  Lemma own_inv_acc E N c P :
    ↑N ⊆ E → own_inv N c P ⊢
          |={E,E∖↑N}=> ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
    iDestruct 1 as (i) "[Hi #[HiP HiC]]".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    (* iIntros (c' HCR). *)
    (* iDestruct (frag_invariant_insert_intro (inv_pick_transform c') with "HiP") as "HiP'". *)
    (* iDestruct (frag_pick_map_transform_Some_intro with "HiC") as "HiC'";[eauto|]. iClear "HiP HiC". *)
    (* iModIntro. *)
    (* iDestruct (frag_invariant_insert_intro (C_pick c') with "HiP'") as "HiP". *)
    (* iDestruct (frag_pick_map_insert_intro _ _ (C_pick c') with "HiC'") as "HiC". iClear "HiP' HiC'". *)
    (* iModIntro. *)
    rewrite {1 4}(union_difference_L (↑ N) E) // wsat.ownE_op; last set_solver.
    rewrite {1 5}(union_difference_L {[ i ]} (↑ N)) // wsat.ownE_op; last set_solver.
    iIntros "(Hw & [HE $] & $) !> !>".
    iDestruct (ownI_open i with "[$Hw $HE $HiP $HiC]") as "($ & $ & HD)".
    iIntros "HP [Hw $] !> !>". iApply (ownI_close _ c P). by iFrame "∗ #".
  Qed.

  Lemma fresh_inv_name (E : gset positive) N : ∃ i, i ∉ E ∧ i ∈ (↑N:coPset).
  Proof.
    exists (coPpick (↑ N ∖ gset_to_coPset E)).
    rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
    apply coPpick_elem_of=> Hfin.
    eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
    apply gset_to_coPset_finite.
  Qed.

  Lemma own_inv_alloc N E c P : inv_cond P c ∗ ▷ P ={E}=∗ own_inv N c P.
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
    iIntros "[#Hcond HP] [Hw $]".
    iMod (ownI_alloc (.∈ (↑N : coPset)) P with "[$HP $Hw $Hcond]")
      as (i ?) "[$ [? ?]]"; auto using fresh_inv_name.
    do 2 iModIntro. iExists i. auto.
  Qed.

  (* This does not imply [own_inv_alloc] due to the extra assumption [↑N ⊆ E]. *)
  Lemma own_inv_alloc_open N E c P :
    ↑N ⊆ E → inv_cond P c ⊢ |={E, E∖↑N}=> own_inv N c P ∗ (▷ P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (Sub) "#Hcond".
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
    iIntros "[Hw HE]".
    iMod (ownI_alloc_open (.∈ (↑N : coPset)) P with "[$Hcond $Hw]")
      as (i ?) "(Hw & #Hi & #Hc & HD)"; auto using fresh_inv_name.
    iAssert (ownE {[i]} ∗ ownE (↑ N ∖ {[i]}) ∗ ownE (E ∖ ↑ N))%I
      with "[HE]" as "(HEi & HEN\i & HE\N)".
    { rewrite -?wsat.ownE_op; [|set_solver..].
      rewrite assoc_L -!union_difference_L //. set_solver. }
    do 2 iModIntro. iFrame "HE\N". iSplitL "Hw HEi"; first by iApply "Hw".
    iSplitL "Hi".
    { iExists i. auto. }
    iIntros "HP [Hw HE\N]".
    iDestruct (ownI_close with "[$Hw $Hi $Hc $HP $HD]") as "[$ HEi]".
    do 2 iModIntro. iSplitL; [|done].
    iCombine "HEi HEN\i HE\N" as "HEN".
    rewrite -?wsat.ownE_op; [|set_solver..].
    rewrite assoc_L -!union_difference_L //; set_solver.
  Qed.

  Lemma own_inv_to_inv M c P : own_inv M c P -∗ inv M c P.
  Proof.
    iIntros "#I". rewrite inv_unseal. auto.
  Qed.

  Lemma own_inv_to_sem_inv M c P : own_inv M c P -∗ inv_sem M c P.
  Proof.
    iIntros "#I". rewrite inv_sem_unseal.
    iIntros (E H). iPoseProof (own_inv_acc with "I") as "H";[eauto|].
    auto.
  Qed.

  Lemma inv_to_sem_inv M c P : inv M c P -∗ inv_sem M c P.
  Proof.
    rewrite inv_unseal.
    iIntros "Hown".
    iDestruct (own_inv_to_sem_inv with "Hown") as "$".
  Qed.

  (** ** Public API of invariants *)
  Global Instance inv_contractive N c : Contractive (inv N c).
  Proof.
    rewrite inv_unseal.
    rewrite /own_inv /=. intros ??? Hdist.
    solve_contractive.
  Qed.

  Global Instance inv_ne N c : NonExpansive (inv N c).
  Proof. apply contractive_ne, _. Qed.

  Global Instance inv_proper N c : Proper (equiv ==> equiv) (inv N c).
  Proof. apply ne_proper, _. Qed.

  Global Instance inv_persistent N c P : Persistent (inv N c P).
  Proof. rewrite inv_unseal. apply _. Qed.

  Global Instance inv_sem_contractive N c : Contractive (inv_sem N c).
  Proof.
    rewrite inv_sem_unseal.
    rewrite /inv_def /=. intros ??? Hdist.
    solve_contractive.
  Qed.

  Global Instance inv_sem_ne N c : NonExpansive (inv_sem N c).
  Proof. apply contractive_ne, _. Qed.

  Global Instance inv_sem_proper N c : Proper (equiv ==> equiv) (inv_sem N c).
  Proof. apply ne_proper, _. Qed.

  Global Instance inv_sem_persistent N c P : Persistent (inv_sem N c P).
  Proof. rewrite inv_sem_unseal. apply _. Qed.

  Lemma inv_mod_intro N c P c' :
    CR c c' ->
    inv N c P ⊢ ⚡={transmap_insert_two_inG (inv_pick_transform c') (C_pick c') Ω}=> inv N c P.
  Proof.
    rewrite inv_unseal /own_inv.
    iIntros (HCR) "#HI".
    iDestruct "HI" as (i Hin) "[HI HC]".
    iDestruct (frag_invariant_insert_two_intro with "HI") as "HI'".
    iDestruct (frag_pick_map_transform_two_Some_intro with "HC") as "HC'";[eauto|].
    iClear "HI HC". iModIntro. iExists _. iFrame "# %".
  Qed.
  
  Lemma inv_alter N c P Q : inv_sem N c P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ inv_sem N c Q.
  Proof.
    rewrite inv_sem_unseal. iIntros "#HI #HPQ !>" (E H).
    iMod ("HI" $! E H) as "[HP Hclose]".
    iDestruct ("HPQ" with "HP") as "[$ HQP]".
    iIntros "!> HQ". iApply "Hclose". iApply "HQP". done.
  Qed.

  Lemma inv_iff N c P Q : inv_sem N c P -∗ ▷ □ (P ↔ Q) -∗ inv_sem N c Q.
  Proof.
    iIntros "#HI #HPQ". iApply (inv_alter with "HI").
    iClear "HI". iIntros "!> !> HP". iSplitL "HP".
    - by iApply "HPQ".
    - iIntros "HQ". by iApply "HPQ".
  Qed.

  Lemma inv_alloc N E c P : inv_cond P c ∗ ▷ P ={E}=∗ inv N c P.
  Proof.
    iIntros "[#Hcond HP]". iApply (own_inv_to_inv _ c).
    iApply (own_inv_alloc N E with "[$HP $Hcond]").
  Qed.

  Lemma inv_alloc_open N E c P :
    ↑N ⊆ E → inv_cond P c ⊢ |={E, E∖↑N}=> inv N c P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?) "#Hcond".
    iMod (own_inv_alloc_open with "[$]") as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.

  Lemma inv_acc E N c P :
    ↑N ⊆ E → ⊢ inv N c P →
          |={E,E∖↑N}=> ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "#HI".
    iDestruct (inv_to_sem_inv with "HI") as "HI'".
    rewrite inv_sem_unseal /inv_def.
    by iApply "HI'".
  Qed.

  Lemma inv_combine N1 N2 N c P Q :
    N1 ## N2 →
    ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    inv_sem N1 c P -∗ inv_sem N2 c Q -∗ inv_sem N c (P ∗ Q).
  Proof.
    rewrite inv_sem_unseal. iIntros (??) "#HinvP #HinvQ !>"; iIntros (E ?).
    iMod ("HinvP" $! E with "[%]") as "[$ HcloseQ]";[set_solver|].
    iMod ("HinvQ" $! (E ∖ ↑N1) with "[%]") as "[$ HcloseP]";[set_solver|].
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose [HP HQ]".
    iMod "Hclose" as %_. iMod ("HcloseP" with "HQ") as %_.
    by iApply "HcloseQ".
  Qed.

  Lemma inv_combine_dup_l N c P Q :
    □ (P -∗ P ∗ P) -∗
    inv_sem N c P -∗ inv_sem N c Q -∗ inv_sem N c (P ∗ Q).
  Proof.
    rewrite inv_sem_unseal. iIntros "#HPdup #HinvP #HinvQ !>" (E ?).
    iMod ("HinvP" with "[//]") as "[HP HcloseP]".
    iDestruct ("HinvQ" with "[//]") as "HQ". 
    iDestruct ("HPdup" with "HP") as "[$ HP]".
    iMod ("HcloseP" with "HP") as %_.
    iMod "HQ" as "[$ HcloseQ]".
    iIntros "!> [HP HQ]". by iApply "HcloseQ".
  Qed.

  Lemma except_0_inv N c P : ◇ inv_sem N c P ⊢ inv_sem N c P.
  Proof.
    rewrite inv_sem_unseal /inv_def. iIntros "#H !>" (E HE).
    iSpecialize ("H" $! E HE).
    iMod "H". by iApply "H".
  Qed.

  (** ** Proof mode integration *)
  Global Instance is_except_0_inv N c P : IsExcept0 (inv_sem N c P).
  Proof. apply except_0_inv. Qed.

  Global Instance into_inv_inv N c P : IntoInv (inv N c P) N := {}.
  Global Instance into_inv_sem_inv N c P : IntoInv (inv_sem N c P) N := {}.

  Global Instance into_acc_inv N c P E:
    IntoAcc (X := unit) (inv N c P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _".
    iApply inv_acc;eauto.
  Qed.

  (** ** Derived properties *)
  Lemma inv_acc_strong E N c P :
    ↑N ⊆ E → ⊢ inv N c P →
          |={E,E∖↑N}=> ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
  Proof.
    iIntros (?) "Hinv".
    iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
    iIntros (E') "HP".
    iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
    by rewrite left_id_L.
  Qed.

  Lemma inv_acc_timeless E N c P `{!Timeless P} :
    ↑N ⊆ E → ⊢ inv N c P →
    |={E,E∖↑N}=> P ∗ (P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "Hinv".
    iDestruct (inv_acc with "Hinv") as "H";[eauto|].
    iMod "H" as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  Lemma inv_split_l N c P Q : inv_sem N c (P ∗ Q) -∗ inv_sem N c P.
  Proof.
    iIntros "#HI". iApply inv_alter; eauto.
    iClear "HI". iIntros "!> !> [$ $] $".
  Qed.
  Lemma inv_split_r N c P Q : inv_sem N c (P ∗ Q) -∗ inv_sem N c Q.
  Proof.
    rewrite (comm _ P Q). eapply inv_split_l.
  Qed.
  Lemma inv_split N c P Q : inv_sem N c (P ∗ Q) -∗ inv_sem N c P ∗ inv_sem N c Q.
  Proof.
    iIntros "#H".
    iPoseProof (inv_split_l with "H") as "$".
    iPoseProof (inv_split_r with "H") as "$".
  Qed.

End inv.
