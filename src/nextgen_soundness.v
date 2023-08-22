From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants fancy_updates wsat later_credits.
From iris.prelude Require Import options.

From nextgen Require Import cmra_morphism_extra.
From nextgen Require Export nextgen_basic.
Import uPred.


Lemma bnextgen_fupd_soundness_no_lc_alt `{!invGpreS Σ} (E1 : coPset) (P : iProp Σ) `{!Plain P} m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ} `{ω : coPset → iProp Σ}, £ m ∗ (□ (∀ (E0 E3 : coPset) (P0 : iPropI Σ), (|={E0,E3}=> P0) -∗ ω E0 ==∗ ◇ (ω E3 ∗ P0))) ∗ ω E1 ==∗ ⚡={f}=> P) → ⊢ P.
Proof.
  intros Hfupd. apply later_soundness.
  eapply (bnextgen_plain_soundness f); [by apply later_plain|].
  apply bupd_soundness;[by apply plain_bnextgen_plain,later_plain|].
  iMod fupd_soundness_no_lc_unfold as (hws ω) "(Hlc & Hω & #H)".
  iMod (Hfupd with "[$Hlc $H $Hω]"). iModIntro;iFrame.
  iApply (bnextgen_mono with "[$]"). iIntros "H". iNext. auto.
Qed.

Lemma bnextgen_fupd_soundness_no_lc `{!invGpreS Σ} E1 E2 (P : iProp Σ) `{!Plain P} m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={E1,E2}=∗ ⚡={f}=> P) → ⊢ P.
Proof.
  intros Hfupd. apply later_soundness.
  eapply (bnextgen_plain_soundness f); [by apply later_plain|].
  apply bupd_soundness;[by apply plain_bnextgen_plain,later_plain|].
  iMod fupd_soundness_no_lc_unfold as (hws ω) "(Hlc & Hω & #H)".
  iMod ("H" with "[Hlc] Hω") as "H'".
  { iMod (Hfupd with "Hlc") as "H'". iModIntro. iApply "H'". }
  iDestruct "H'" as "[H1 H2]". rewrite -bnextgen_later.
  iDestruct "H2" as ">H2". iModIntro. iNext. iFrame.
Qed.

Lemma bnextgen_fupd_soundness_lc `{!invGpreS Σ} `{!lcGpreS Σ} `{!wsatGpreS Σ} n E1 E2 (P : iProp Σ) `{!Plain P} (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ n ={E1,E2}=∗ ⚡={f}=> P) → ⊢ P.
Proof.
  intros Hfupd. eapply (le_upd.lc_soundness (S n)); first done.
  intros Hc. rewrite lc_succ.
  iIntros "[Hone Hn]". rewrite -le_upd.le_upd_trans. iApply le_upd.bupd_le_upd.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  set (Hi := InvG HasLc _ Hw Hc).
  iAssert (|={⊤,E2}=> ⚡={f}=> P)%I with "[Hn]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. by iApply (Hfupd Hi). }
  rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
  iModIntro. iMod ("H" with "[$Hw $HE]") as "H".
  iPoseProof (except_0_into_later with "H") as "H".
  iApply (le_upd.le_upd_later with "Hone"). iNext.
  iApply bnextgen_plain. iDestruct "H" as "(_ & _ & $)".
Qed.

Lemma bnextgen_fupd_soundness_gen `{!invGpreS Σ} `{!lcGpreS Σ} `{!wsatGpreS Σ} n hlc E1 E2 (P : iProp Σ) `{!Plain P} (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen hlc Σ}, £ n ={E1,E2}=∗ ⚡={f}=> P) → ⊢ P.
Proof.
  destruct hlc.
  - by apply bnextgen_fupd_soundness_lc.
  - by apply bnextgen_fupd_soundness_no_lc.
Qed.

Lemma bnextgen_step_fupdN_soundness_no_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  intros Hiter.
  apply (laterN_soundness _  (S n)); simpl.
  apply (fupd_soundness_no_lc ⊤ ⊤ _ m)=> Hinv. iIntros "Hc".
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iApply fupd_plainly_mask_empty. iSpecialize ("H" with "Hc").
  iMod (step_fupdN_plain with "H") as "H";[by apply plain_bnextgen_plain|]. iMod "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iDestruct "H" as ">H". iNext.
  iDestruct (bnextgen_plain with "H") as "H".
  iDestruct (plain with "H") as "H". iFrame.
Qed.

Lemma bnextgen_step_fupdN_soundness_no_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤}[∅]▷=∗^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  intros Hiter. eapply (bnextgen_step_fupdN_soundness_no_lc _ n m)=>Hinv.
  iIntros "Hcred". destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod (Hiter with "Hcred") as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.

Lemma bnextgen_step_fupdN_soundness_lc `{!invGpreS Σ} `{!lcGpreS Σ} `{!wsatGpreS Σ} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  intros Hiter.
  eapply (bnextgen_fupd_soundness_lc (m + n)); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iMod (Hiter with "Hm") as "Hupd".
  clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

Lemma bnextgen_step_fupdN_soundness_lc' `{!invGpreS Σ} `{!lcGpreS Σ} `{!wsatGpreS Σ} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGS_gen hlc Σ}, £ m ={⊤}[∅]▷=∗^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  intros Hiter.
  eapply (bnextgen_fupd_soundness_lc (m + n) ⊤ ⊤); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iPoseProof (Hiter with "Hm") as "Hupd".
  clear Hiter.
  (* FIXME can we reuse [step_fupdN_soundness_lc] instead of redoing the induction? *)
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

(** Generic soundness lemma for the fancy update, parameterized by [use_credits]
  on whether to use credits or not. *)
Lemma bnextgen_step_fupdN_soundness_gen `{!invGpreS Σ} `{!lcGpreS Σ} `{!wsatGpreS Σ} (P : iProp Σ) `{!Plain P}
  (hlc : has_lc) (n m : nat) (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv : invGS_gen hlc Σ},
    £ m ={⊤,∅}=∗ |={∅}▷=>^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  destruct hlc.
  - apply bnextgen_step_fupdN_soundness_lc. done.
  - apply bnextgen_step_fupdN_soundness_no_lc. done.
Qed.

Global Instance step_fupdN_ne
  (PROP : bi) (BiFUpd0 : BiFUpd PROP) (Eo Ei : coPset) (n : nat) : (NonExpansive (λ (P : PROP), |={Eo}[Ei]▷=>^n P))%I.
Proof.
  induction n;simpl;try apply _.
  intros m P1 P2 Hm. apply fupd_ne, later_ne, fupd_ne, IHn =>//.
Qed.

Section bnextgen_pred_imod.
  Context {M : ucmra} {A : Type} (f : A -> M → M) `{!forall a, CmraMorphism (f a)} {num_laters_per_step : nat -> nat}
    `{BiFUpd (uPredI M)}.

  Fixpoint bnextgen_n
    (l : list A) (start : nat) (P : uPredI M) : uPredI M :=
    match l with
    | [] => P
    | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) |={∅,⊤}=>
        ⚡={f a}=> (bnextgen_n l' (S start) P)
    end.
  
  Fixpoint bnextgen_n_open
    (l : list A) (start : nat) (P : uPredI M) : uPredI M :=
    match l with
    | [] =>  P
    | a :: l' => |={∅}▷=>^(S $ num_laters_per_step start)
                          ⚡={f a}=> (bnextgen_n_open l' (S start) P)
    end.

  Notation "⚡={[ l ]}▷=>^ ( n ) P" := (bnextgen_n l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope.

  Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (bnextgen_n_open l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope.

 
  Lemma bnextgen_n_mono P Q l n :
    (P ⊢ Q) → (⚡={[ l ]}▷=>^(n) P) ⊢ (⚡={[ l ]}▷=>^(n) Q).
  Proof.
    intros Hi. revert n; induction l =>n;auto.
    iIntros "H". simpl.
    iMod "H". iModIntro.
    iApply (step_fupdN_mono with "H"). iIntros "H".
    iMod "H". iModIntro. iApply (bnextgen_mono with "H"). iApply IHl.
  Qed.

  Lemma bnextgen_n_open_mono P Q l n :
    (P ⊢ Q) → (⚡={[ l ]}▷=>>^(n) P) ⊢ (⚡={[ l ]}▷=>>^(n) Q).
  Proof.
    intros Hi. revert n; induction l =>n;auto.
    iIntros "H". simpl.
    iMod "H". iModIntro.
    iApply (step_fupdN_mono with "H"). iIntros "H".
    iModIntro. iApply IHl. auto.
  Qed.

  Global Instance bnextgen_n_mono' l n :
    Proper ((⊢) ==> (⊢)) (bnextgen_n l n).
  Proof. intros P Q. apply bnextgen_n_mono. Qed.

  Global Instance bnextgen_n_open_mono' l n :
    Proper ((⊢) ==> (⊢)) (bnextgen_n_open l n).
  Proof. intros P Q. apply bnextgen_n_open_mono. Qed.

  Global Instance nextgen_n_ne l n : NonExpansive (bnextgen_n l n).
  Proof.
    revert n; induction l =>n;simpl;auto;try apply _.
    (* { apply fupd_ne. } *)
    intros x P Q Hne.
    destruct H with a. simpl in *.
    apply fupd_ne.
    apply fupd_ne,later_ne, fupd_ne.
    apply step_fupdN_ne. apply fupd_ne.
    apply bnextgen_ne.  apply IHl. auto.
  Qed.

  Global Instance bnextgen_n_proper l n :
    Proper ((≡) ==> (≡)) (bnextgen_n l n) := ne_proper _.

  Lemma bnextgen_n_open_snoc l x n P :
    (⚡={[(l ++ [x])]}▷=>>^(n) P) ⊣⊢ ⚡={[l]}▷=>>^(n) (|={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) ⚡={f x}=> P).
  Proof.
    revert n; induction l => n.
    - simpl. iSplit; iIntros "H"; rewrite Nat.add_0_r; auto.
    - simpl. iSplit;iIntros ">H".
      all: iModIntro.
      all: iApply (step_fupdN_mono with "H"); iIntros "H".
      all: iApply (bnextgen_mono with "H"); iIntros "H".
      + iDestruct (IHl with "H") as "H".
        rewrite Nat.add_succ_r. iFrame.
      + iApply IHl. rewrite Nat.add_succ_r. iFrame.
  Qed.

  Lemma bnextgen_n_snoc l x n P :
    (⚡={[(l ++ [x])]}▷=>^(n) P) ⊣⊢ ⚡={[l]}▷=>^(n) (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) |={∅,⊤}=> ⚡={f x}=> P).
  Proof.
    revert n; induction l => n.
    - simpl. iSplit; iIntros "H"; rewrite Nat.add_0_r; auto. (* rewrite fupd_trans. auto. *)
    - simpl. iSplit;iIntros ">H".
      all: iModIntro.
      all: iApply (step_fupdN_mono with "H"); iIntros "H".
      all: iApply (bnextgen_mono with "H"); iIntros "H".
      + iDestruct (IHl with "H") as "H".
        rewrite Nat.add_succ_r. iFrame.
      + iApply IHl. rewrite Nat.add_succ_r. iFrame.
  Qed.

End bnextgen_pred_imod.

Lemma bnextgen_fupd_elim_no_lc `{!invGpreS Σ} `{Hinv: !invGS_gen HasNoLc Σ} E1 E2 (P : iProp Σ) `{!Plain P} (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (|={E1,E2}=> ⚡={f}=> P) ⊢ |={E1,E2}=> P.
Proof.
  iIntros "Hm".
  iMod "Hm". iModIntro.
  iApply bnextgen_plain. eauto.
Qed.

Lemma fupd_soundness_no_lc_unfold_alt `{!invGpreS Σ} `{!lcGpreS Σ} `{!wsatGpreS Σ} m E :
  ⊢ |==> ∃ `(Hws: invGS_gen HasNoLc Σ) (ω : coPset → iProp Σ),
    £ m ∗ ω E ∗ ■ (∀ E1 E2 P n, (|={E1}[E2]▷=>^n P) -∗ ω E1 -∗ Nat.iter n (λ P, |==> ▷ |==> ▷ P) (ω E1 ∗ P)).
Proof.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  (* We don't actually want any credits, but we need the [lcGS]. *)
  iMod (later_credits.le_upd.lc_alloc m) as (Hc) "[_ Hlc]".
  set (Hi := InvG HasNoLc _ Hw Hc).
  iExists Hi, (λ E, wsat ∗ ownE E)%I.
  rewrite (union_difference_L E ⊤); [|set_solver].
  rewrite ownE_op; [|set_solver].
  iDestruct "HE" as "[HE _]". iFrame.
  iIntros "!>!>" (E1 E2 P n) "HP HwE".
  iInduction (n) as [|n] "IH" forall (P).
  - simpl. iFrame.
  - assert ((S n) = n + 1) as ->;[lia|].
    rewrite step_fupdN_add.
    iDestruct ("IH" with "HP HwE") as "t". simpl.
    rewrite PeanoNat.Nat.add_1_r.
    rewrite Nat.iter_succ_r.
    iApply (iter_modal_mono with "[] t").
    { intros. iIntros "H H'". iMod "H'". iIntros "!>!>".
      iMod "H'". iIntros "!>!>". iApply "H". auto. }
    iIntros "[HwE HP]".
    rewrite fancy_updates.uPred_fupd_unseal
      /fancy_updates.uPred_fupd_def -assoc /=.
    iMod ("HP" with "HwE") as ">[Hwsat [HwE HP]]".
    iDestruct ("HP" with "[$Hwsat $HwE]") as "Hr".
    iModIntro. iNext. iMod "Hr". iModIntro. iMod "Hr". iNext. auto.
Qed.

Lemma bupd_laterN_plain_interweave :
  ∀ {PROP : bi} {BiBUpd0 : BiBUpd PROP} {BiPlainly0 : BiPlainly PROP},
    BiBUpdPlainly PROP → ∀ (P : PROP) (n : nat), Plain P → (Nat.iter n (λ P, |==> ▷ |==> ▷ P) P) ⊢ ▷^(n + n) P.
Proof.
  intros. iIntros "Hn".
  iInduction n as [|n] "IH".
  - simpl;auto.
  - simpl. iApply bupd_plain. iMod "Hn". iModIntro. iNext.
    iApply bupd_plain. iMod "Hn". iModIntro.
    rewrite Nat.add_succ_r /=. iNext. iApply "IH". iFrame.
Qed.

Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
      S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Section bnextgen_n_open_soundness.
  Context {A : Type} {Σ : gFunctors} (f : A -> iResUR Σ → iResUR Σ) `{!forall a, CmraMorphism (f a)}
    {num_laters_per_step : nat -> nat}.

  Notation "⚡={[ l ]}▷=>^ ( n ) P" := (@bnextgen_n _ _ f _ num_laters_per_step _ l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope.

  Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (@bnextgen_n_open _ _ f _ num_laters_per_step _ l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope.

  Lemma step_fupdN_nextgen_soundness_no_lc (l : list A) :
    invGpreS Σ → ∀ P : iProp Σ,
        Plain P → ∀ (n m : nat), (∀ (Hinv : invGS_gen HasNoLc Σ), £ m -∗ ⚡={[l]}▷=>>^(n) (* |={⊤,∅}=> *) P) → (⊢ P)%stdpp.
  Proof.
    intros until P. intros HPlain n m  Hiter.
    apply (laterN_soundness _ (steps_sum num_laters_per_step (n) (S (length l)) + steps_sum num_laters_per_step (n) (S (length l)))).
    iMod (fupd_soundness_no_lc_unfold_alt (m + (steps_sum num_laters_per_step (n) (length l))) ∅) as (Hws ω) "[Hm [Hω #H]]".
    specialize (Hiter Hws).
    rewrite lc_split. iDestruct "Hm" as "[Hm Hn]".
    iDestruct (Hiter with "Hm") as "HH". clear Hiter.
    iStopProof. revert n. induction l;intros n;iIntros "[#H (Hn & Hω & HH)]".
    - simpl. auto.
    - simpl. rewrite /= -Nat.add_succ_r.
      iDestruct "Hn" as "[Hone [Hm Hn]]".
      iAssert (|={∅}▷=>^(S $ num_laters_per_step n) ⚡={f a}=> ⚡={[l]}▷=>>^(S n) P)%I with "HH" as "HH".
      iDestruct ("H" with "HH Hω") as "HH".

      set (num:=S (num_laters_per_step (S n) + steps_sum num_laters_per_step (S (S n)) (length l))).
      rewrite -plus_Sn_m Nat.add_assoc.
      rewrite -later_laterN -!plus_Sn_m.
      assert (S (num_laters_per_step n) + num + S (num_laters_per_step n) + num =
                S (num_laters_per_step n) + S (num_laters_per_step n) + (num + num)) as ->;[lia|].
      rewrite laterN_add.
      iApply bupd_laterN_plain_interweave.
      iApply (iter_modal_mono with "[-HH] HH").
      { intros. iIntros "J H". iMod "H". iIntros "!>!>".
        iMod "H". iIntros "!>!>". iApply "J". iFrame. }
      iIntros "[Hω HP]".
      iApply (bnextgen_plain (f a)).
      iAssert (⚡={f a}=> ω ∅)%I with "[Hω]" as "HA1";[admit|].
      iAssert (⚡={f a}=> £ (steps_sum num_laters_per_step (S n) (length l)))%I with "[Hn]" as "HA2";[admit|].
      iModIntro.
      iDestruct (IHl with "[$H $HA1 $HA2 $HP]") as "HH".
      rewrite /num. simpl. iNext. iApply (laterN_mono with "HH"). auto.
  Admitted.
      

End bnextgen_n_open_soundness.
