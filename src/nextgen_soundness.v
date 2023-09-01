From iris.proofmode Require Import classes tactics proofmode.
From iris.base_logic.lib Require Export iprop own later_credits.
From iris.prelude Require Import options.
From stdpp Require Export coPset.

From iris.algebra Require Import gmap_view gset coPset.

From nextgen Require Import cmra_morphism_extra.
From nextgen.lib Require Import wsat fancy_updates.
From nextgen Require Export nextgen_basic nextgen_pointwise.
Import uPred.

Local Lemma lc_alloc `{!lcGIndpreS Σ Ω} n :
  ⊢ |==> ∃ _ : lcGIndS Σ Ω, later_credits.lc_supply n ∗ £ n.
Proof.
  set (WW:=lcGIndpreS0).
  destruct lcGIndpreS0.
  rewrite later_credits.lc_unseal /later_credits.lc_def later_credits.lc_supply_unseal /later_credits.lc_supply_def.
  iMod (own_alloc (● n ⋅ ◯ n)) as (γLC) "[H● H◯]";
    first (apply auth_both_valid; split; done).
  pose (C := LcGIndS _ _ lcGpreS_inG γLC).
  iModIntro. iExists C. iFrame.
Qed.

Local Lemma fupd_unfold_implies `{!invGIndS_gen HasNoLc Σ Ω} `{!noTransInG Σ Ω T} ω :
  ■ (∀ (E1 E2 : coPset) (P : iPropI Σ), (|={E1,E2}=> P) -∗ ω E1 ==∗ ◇ (ω E2 ∗ P)) ⊢
  ■ (∀ E1 E2 P n, (|={E1}[E2]▷=>^n P) -∗ ω E1 -∗ Nat.iter n (λ P, |==> ▷ |==> ▷ P) (ω E1 ∗ P)).
Proof.
  iIntros "#H".
  iModIntro.
  iIntros (E1 E2 P n).
  iRevert (E1 E2 P).
  iStopProof. induction n.
  - iIntros "#H". iIntros (E1 E2 P) "HP Hω".
    simpl. iFrame.
  - iIntros "#H".
    iDestruct (IHn with "H") as "IH".
    iIntros (E1 E2 P) "HP Hω".
    simpl.
    iMod ("H" with "HP Hω") as ">[Hω HP]".
    iModIntro. iNext.
    iMod ("H" with "HP Hω") as ">[Hω HP]".
    iModIntro. iNext. iApply ("IH" with "HP Hω").
Qed.
    
   
Local Lemma fupd_soundness_no_lc_unfold_alt `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} m E :
  ⊢ |==> ∃ `(Hws: invGIndS_gen HasNoLc Σ Ω) (ω : coPset -> iProp Σ),
      £ m ∗ ω E
        ∗ ■ (∀ (E1 E2 : coPset) (P : iPropI Σ), (|={E1,E2}=> P) -∗ ω E1 ==∗ ◇ (ω E2 ∗ P))
        ∗ ■ (∀ E (t : T → T) `{!CmraMorphism t}, ω E -∗ ⚡={transmap_insert_inG t Ω}=> ω E).
Proof.
  destruct invGIndpreS0.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  (* We don't actually want any credits, but we need the [lcGS]. *)
  iMod (lc_alloc m) as (Hc) "[Hsupply Hm]".
  set (Hi := InvIndG HasNoLc _ Ω Hw Hc).
  iExists Hi, (λ E, wsat ∗ ownE E)%I.
  rewrite (union_difference_L E ⊤); [|set_solver].
  rewrite wsat.ownE_op; [|set_solver]. iFrame.
  iDestruct "HE" as "[HE _]". iFrame.
  iModIntro. iSplit.
  { iIntros "!>" (E1 E2 P) "HP [Hw HE]".
    rewrite fancy_updates.uPred_fupd_unseal
          /fancy_updates.uPred_fupd_def -assoc /=.
    iMod ("HP" with "[$Hw $HE]") as ">(Hw & HE & HP)". by iFrame. }
  { iModIntro. iIntros (E1 t ?) "[Hw HE]".
    iDestruct (wsat_ind_insert_intro with "Hw") as "Hw".
    iDestruct (ownE_ind_insert_intro with "HE") as "HE".
    iModIntro. iFrame. }
Qed.

Local Lemma fupd_soundness_no_lc_unfold `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} m E :
  ⊢ |==> ∃ `(Hws: invGIndS_gen HasNoLc Σ Ω) (ω : coPset → iProp Σ),
    £ m ∗ ω E ∗ □ (∀ E1 E2 P, (|={E1, E2}=> P) -∗ ω E1 ==∗ ◇ (ω E2 ∗ P)).
Proof.
  iMod fupd_soundness_no_lc_unfold_alt as (Hws ω) "(?&?&?&?)".
  iExists Hws,ω. iModIntro. iFrame. eauto.
Qed.

Local Lemma lc_soundness `{!lcGIndpreS Σ Ω} m (P : iProp Σ) `{!Plain P} :
  (∀ {Hc: lcGIndS Σ Ω}, £ m -∗ le_upd.le_upd P) → ⊢ P.
Proof.
  set (WW:=lcGIndpreS0).
  destruct lcGIndpreS0.
  intros H. apply (laterN_soundness _ (S m)).
  eapply bupd_soundness; first apply _.
  iStartProof.
  iMod (lc_alloc m) as (C) "[H● H◯]".
  iPoseProof (H C) as "Hc". iSpecialize ("Hc" with "[$H◯]").
  iPoseProof (le_upd.le_upd_elim_complete m with "H● Hc") as "H".
  simpl. iMod "H". iModIntro. iNext.
  clear H. iInduction m as [|m] "IH"; simpl; [done|].
  iMod "H". iNext. by iApply "IH".
Qed.

Local Notation "⚡={ f }=> P" := (uPred_bnextgen f P)
                            (at level 99, f at level 50, P at level 200, format "⚡={ f }=>  P") : bi_scope.

Lemma bnextgen_fupd_soundness_no_lc `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} E1 E2 (P : iProp Σ) `{!Plain P} m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f}:
  (∀ `{Hinv: !invGIndS_gen HasNoLc Σ Ω}, £ m ={E1,E2}=∗ ⚡={f}=> P) → ⊢ P.
Proof.
  intros Hfupd. apply later_soundness.
  eapply (bnextgen_plain_soundness); [by apply later_plain|].
  apply bupd_soundness;[by apply plain_bnextgen_plain,later_plain|].
  iMod fupd_soundness_no_lc_unfold as (hws ω) "(Hlc & Hω & #H)".
  iMod ("H" with "[Hlc] Hω") as "H'".
  { iMod (Hfupd with "Hlc") as "H'". iModIntro. iApply "H'". }
  iDestruct "H'" as "[H1 H2]". rewrite -bnextgen_later.
  iDestruct "H2" as ">H2". iModIntro. iNext. iFrame.
Qed.

Lemma bnextgen_fupd_soundness_lc `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} n E1 E2 (P : iProp Σ) `{!Plain P} (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGIndS_gen HasLc Σ Ω}, £ n ={E1,E2}=∗ ⚡={f}=> P) → ⊢ P.
Proof.
  destruct invGIndpreS0.
  intros Hfupd. eapply (lc_soundness (S n)); first done.
  intros Hc. rewrite lc_succ.
  iIntros "[Hone Hn]". rewrite -le_upd.le_upd_trans. iApply le_upd.bupd_le_upd.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  set (Hi := InvIndG HasLc _ _ Hw Hc).
  iAssert (|={⊤,E2}=> ⚡={f}=> P)%I with "[Hn]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. by iApply (Hfupd Hi). }
  rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
  iModIntro. iMod ("H" with "[$Hw $HE]") as "H".
  iPoseProof (except_0_into_later with "H") as "H".
  iApply (le_upd.le_upd_later with "Hone"). iNext.
  iApply bnextgen_plain. iDestruct "H" as "(_ & _ & $)".
Qed.

Lemma bnextgen_fupd_soundness_gen `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} n hlc E1 E2 (P : iProp Σ) `{!Plain P} (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGIndS_gen hlc Σ Ω}, £ n ={E1,E2}=∗ ⚡={f}=> P) → ⊢ P.
Proof.
  inversion invGIndpreS0.
  destruct hlc.
  - by apply bnextgen_fupd_soundness_lc.
  - by apply bnextgen_fupd_soundness_no_lc.
Qed.

Local Lemma fupd_soundness_no_lc `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} E1 E2 (P : iProp Σ) `{!Plain P} m :
  (∀ `{Hinv: !invGIndS_gen HasNoLc Σ Ω}, £ m ={E1,E2}=∗ P) → ⊢ P.
Proof.
  intros Hfupd. apply later_soundness, bupd_soundness; [by apply later_plain|].
  iMod fupd_soundness_no_lc_unfold as (hws ω) "(Hlc & Hω & #H)".
  iMod ("H" with "[Hlc] Hω") as "H'".
  { iMod (Hfupd with "Hlc") as "H'". iModIntro. iApply "H'". }
  iDestruct "H'" as "[>H1 >H2]". by iFrame.
Qed.

Lemma bnextgen_step_fupdN_soundness_no_lc `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGIndS_gen HasNoLc Σ Ω}, £ m ={⊤,∅}=∗ |={∅}▷=>^n ⚡={f}=> P) →
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

Lemma bnextgen_step_fupdN_soundness_no_lc' `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGIndS_gen HasNoLc Σ Ω}, £ m ={⊤}[∅]▷=∗^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  intros Hiter. eapply (bnextgen_step_fupdN_soundness_no_lc _ n m)=>Hinv.
  iIntros "Hcred". destruct n as [|n].
  { by iApply fupd_mask_intro_discard; [|iApply (Hiter Hinv)]. }
   simpl in Hiter |- *. iMod (Hiter with "Hcred") as "H". iIntros "!>!>!>".
  iMod "H". clear. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.


Lemma bnextgen_step_fupdN_soundness_lc `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGIndS_gen HasLc Σ Ω}, £ m ={⊤,∅}=∗ |={∅}▷=>^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  inversion invGIndpreS0.
  intros Hiter.
  eapply (bnextgen_fupd_soundness_lc (m + n)); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iMod (Hiter with "Hm") as "Hupd".
  clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (fancy_updates.lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

Lemma bnextgen_step_fupdN_soundness_lc' `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} (P : iProp Σ) `{!Plain P} n m (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv: !invGIndS_gen hlc Σ Ω}, £ m ={⊤}[∅]▷=∗^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  inversion invGIndpreS0.
  intros Hiter.
  eapply (bnextgen_fupd_soundness_lc (m + n) ⊤ ⊤); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iPoseProof (Hiter with "Hm") as "Hupd".
  clear Hiter.
  (* FIXME can we reuse [step_fupdN_soundness_lc] instead of redoing the induction? *)
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (fancy_updates.lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

(** Generic soundness lemma for the fancy update, parameterized by [use_credits]
  on whether to use credits or not. *)
Lemma bnextgen_step_fupdN_soundness_gen `{!invGIndpreS Σ Ω} `{!noTransInG Σ Ω T} (P : iProp Σ) `{!Plain P}
  (hlc : has_lc) (n m : nat) (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (∀ `{Hinv : invGIndS_gen hlc Σ Ω},
    £ m ={⊤,∅}=∗ |={∅}▷=>^n ⚡={f}=> P) →
  ⊢ P.
Proof.
  inversion invGIndpreS0.
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

Lemma bnextgen_fupd_elim `{!invGpreS Σ} `{Hinv: !invGS_gen hlc Σ} E1 E2 (P : iProp Σ) `{!Plain P} (f : iResUR Σ -> iResUR Σ) `{GenTrans (iResUR Σ) f} :
  (|={E1,E2}=> ⚡={f}=> P) ⊢ |={E1,E2}=> P.
Proof.
  iIntros "Hm".
  iMod "Hm". iModIntro.
  iApply bnextgen_plain. eauto.
Qed.

Lemma step_fupdN_sep (PROP : bi) (BiFUpd0 : BiFUpd PROP) (E : coPset) n (P Q : PROP) :
  (|={E}▷=>^n P) ∗ (|={E}▷=>^n Q) ⊢ |={E}▷=>^n P ∗ Q.
Proof.
  induction n.
  - simpl. auto.
  - simpl. iIntros "[H1 H2]".
    iMod "H1". iMod "H2".
    iIntros "!>!>".
    iMod "H1". iMod "H2".
    iModIntro. iApply IHn. iFrame.
Qed.

Local Notation "⚡={ M }=> P" := (nextgen_omega M P)
  (at level 99, M at level 50, P at level 200, format "⚡={ M }=>  P") : bi_scope.

Section bnextgen_pred_imod.
  Context {Σ : gFunctors} {Ω : gTransformations Σ} {A : Type} `{!noTransInG Σ Ω C} (f : A -> C → C) `{!forall a, CmraMorphism (f a)} {num_laters_per_step : nat -> nat}
  `{!invGIndS_gen hlc Σ Ω}.

  
  Fixpoint bnextgen_repeat_n
    (l : list A) (P : iProp Σ) : iProp Σ :=
    match l with
    | [] => P
    | a :: l' => ⚡={transmap_insert_inG (f a) Ω}=> (bnextgen_repeat_n l' P)
    end.
  
  Fixpoint bnextgen_n
    (l : list A) (start : nat) (P : iProp Σ) : iProp Σ :=
    match l with
    | [] => P
    | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) |={∅,⊤}=>
        ⚡={transmap_insert_inG (f a) Ω}=> (bnextgen_n l' (S start) P)
    end.
  
  Fixpoint bnextgen_n_open
    (l : list A) (start : nat) (P : iProp Σ) : iProp Σ :=
    match l with
    | [] =>  P
    | a :: l' => |={∅}▷=>^(S $ num_laters_per_step start)
                          ⚡={transmap_insert_inG (f a) Ω}=> (bnextgen_n_open l' (S start) P)
    end.

  Notation "⚡={[ l ]}=> P" := (bnextgen_repeat_n l P)
         (at level 99, l at level 50, P at level 200, format "⚡={[ l ]}=> P") : bi_scope.
  
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
    (⚡={[(l ++ [x])]}▷=>>^(n) P) ⊣⊢ ⚡={[l]}▷=>>^(n) (|={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) ⚡={transmap_insert_inG (f x) Ω}=> P).
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
    (⚡={[(l ++ [x])]}▷=>^(n) P) ⊣⊢ ⚡={[l]}▷=>^(n) (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) |={∅,⊤}=> ⚡={transmap_insert_inG (f x) Ω}=> P).
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
  
  Lemma bnextgen_n_sep l n P Q :
    (⚡={[ l ]}▷=>>^(n) P) ∗ (⚡={[ l ]}▷=>^(n) Q) -∗ ⚡={[ l ]}▷=>^(n) P ∗ Q.
  Proof.
    revert n; induction l =>n.
    - simpl. iIntros "H". auto.
    - simpl. iIntros "[H1 H2]".
      iMod "H2". iModIntro.
      iDestruct (step_fupdN_sep _ _ _ (S $ num_laters_per_step n) with "[H1 H2]") as "H".
      { simpl. iFrame. }
      iApply (step_fupdN_wand with "H").
      iIntros "[H1 H2]".
      iMod "H1". iModIntro. iModIntro. iApply IHl.
      iFrame.
  Qed.

  Lemma bnextgen_n_sep_nextgen l n P Q :
    (⚡={[ l ]}=> P) ∗ (⚡={[ l ]}▷=>^(n) Q) -∗ ⚡={[ l ]}▷=>^(n) P ∗ Q.
  Proof.
    revert n; induction l =>n.
    - simpl. iIntros "H". auto.
    - simpl. iIntros "[H1 H2]".
      iMod "H2". iModIntro.
      iApply (step_fupdN_wand with "H2").
      iNext. iIntros "H2".
      iMod "H2". iModIntro. iModIntro. iApply IHl.
      iFrame.
  Qed.

  Lemma bnextgen_n_open_emp_intro P l n :
    (⊢ P) -> ⊢ (⚡={[ l ]}▷=>>^(n) P).
  Proof.
    intros HP.
    revert n; induction l =>n;simpl;auto.
    iApply step_fupdN_intro;auto.
    iModIntro. iNext. iModIntro.
    iNext. iModIntro. iStopProof;eauto.
    apply IHl.
  Qed.

  Lemma bnextgen_n_emp_intro P l n :
    (⊢ P) -> ⊢ (⚡={[ l ]}▷=>^(n) P).
  Proof.
    intros HP.
    revert n; induction l =>n;simpl;auto.
    iApply step_fupdN_intro;auto.
    iApply fupd_mask_intro;auto. iIntros "Hcls".
    iModIntro. iNext. iModIntro.
    iNext. iMod "Hcls". iModIntro. iModIntro. iStopProof;eauto.
    apply IHl.
  Qed.

  Lemma bnextgen_repeat_n_emp_intro P l :
    (⊢ P) -> ⊢ (⚡={[ l ]}=> P).
  Proof.
    intros HP.
    induction l;simpl;auto.
    iModIntro. auto.
  Qed.
    
End bnextgen_pred_imod.

Lemma bupd_laterN_plain_interweave :
  ∀ {PROP : bi} {BiBUpd0 : BiBUpd PROP} {BiPlainly0 : BiPlainly PROP},
    BiBUpdPlainly PROP → ∀ (P : PROP) (n : nat), Plain P → (Nat.iter n (λ P, |==> ▷ |==> ▷ P) P) ⊢ ▷^(n + n) P.
Proof.
  intros. iIntros "Hn".
  iInduction n as [|n] "IH".
  - simpl;auto.
  - simpl. iApply bupd_elim. iMod "Hn". iModIntro. iNext.
    iApply bupd_elim. iMod "Hn". iModIntro.
    rewrite Nat.add_succ_r /=. iNext. iApply "IH". iFrame.
Qed.

Lemma bupd_laterN_plain :
  ∀ {PROP : bi} {BiBUpd0 : BiBUpd PROP} {BiPlainly0 : BiPlainly PROP},
    BiBUpdPlainly PROP → ∀ (P : PROP) (n : nat), Plain P → (Nat.iter n (λ P, |==> ▷ P) P) ⊢ ▷^(n) P.
Proof.
  intros. iIntros "Hn".
  iInduction n as [|n] "IH".
  - simpl;auto.
  - simpl. iApply bupd_elim. iMod "Hn". iModIntro. iNext.
    iApply "IH". iFrame.
Qed.


Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
      S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Section bnextgen_n_open_soundness.
  Context {A : Type} {Σ : gFunctors} {Ω : gTransformations Σ} `{!noTransInG Σ Ω C} (f : A -> C → C) `{!forall (a : A), CmraMorphism (f a)}
    {num_laters_per_step : nat -> nat}.

  Notation "⚡={[ l ]}▷=>^ ( n ) P" := (@bnextgen_n _ _ _ _ _ f _ num_laters_per_step _ _ l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope.

  Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (@bnextgen_n_open _ _ _ _ _ f _ num_laters_per_step _ _ l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope.

  Lemma step_fupdN_nextgen_open_soundness_no_lc (l : list A) :
    invGIndpreS Σ Ω → ∀ P : iProp Σ,
        Plain P → ∀ (n m : nat), (∀ (Hinv : invGIndS_gen HasNoLc Σ Ω), £ m -∗ ⚡={[l]}▷=>>^(n) P) → (⊢ P)%stdpp.
  Proof.
    intros until P. intros HPlain n m  Hiter.
    apply (laterN_soundness _ (steps_sum num_laters_per_step (n) (S (length l)) + steps_sum num_laters_per_step (n) (S (length l)))).
    iMod (fupd_soundness_no_lc_unfold_alt (m + (steps_sum num_laters_per_step (n) (length l))) ∅) as (Hws ω) "[Hm [Hω [#H #H']]]".
    specialize (Hiter Hws).
    rewrite lc_split. iDestruct "Hm" as "[Hm Hn]".
    iDestruct (Hiter with "Hm") as "HH". clear Hiter.
    iStopProof. revert n. induction l;intros n;iIntros "[#[H Hintro] (Hn & Hω & HH)]".
    - simpl. auto.
    - simpl. rewrite /= -Nat.add_succ_r.
      iDestruct "Hn" as "[Hone [Hm Hn]]".
      iDestruct (@fupd_unfold_implies Σ Ω Hws C noTransInG0 ω with "H") as "#H'".
      iAssert (|={∅}▷=>^(S $ num_laters_per_step n) ⚡={transmap_insert_inG (f a) Ω}=> ⚡={[l]}▷=>>^(S n) P)%I with "HH" as "HH".
      iDestruct ("H'" with "HH Hω") as "HH".
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
      iApply (transmap_plain (transmap_insert_inG (f a) Ω)).
      iAssert (⚡={transmap_insert_inG (f a) Ω}=> ω ∅)%I with "[Hω]" as "HA1".
      { iApply "Hintro". iFrame. }
      iModIntro.
      iDestruct (IHl with "[$H $HA1 $Hn $HP $Hintro]") as "HH".
      rewrite /num. simpl. iNext. iApply (laterN_mono with "HH"). auto.
  Qed.


  Lemma step_fupdN_nextgen_soundness_no_lc (l : list A) :
    invGIndpreS Σ Ω → ∀ P : iProp Σ,
        Plain P → ∀ (n m : nat), (∀ (Hinv : invGIndS_gen HasNoLc Σ Ω), £ m ={⊤}=∗ ⚡={[l]}▷=>^(n) |={⊤,∅}=> P) → (⊢ P)%stdpp.
  Proof.
    intros until P. inversion H0. intros HPlain n m  Hiter.
    apply (laterN_soundness _ (steps_sum num_laters_per_step (n) (S (length l)) + steps_sum num_laters_per_step (n) (S (length l)))).
    iMod (fupd_soundness_no_lc_unfold_alt (m + (steps_sum num_laters_per_step (n) (length l))) ⊤) as (Hws ω) "[Hm [Hω [#H #H']]]".
    specialize (Hiter Hws).
    rewrite lc_split. iDestruct "Hm" as "[Hm Hn]".
    iDestruct (Hiter with "Hm") as "HH". clear Hiter.
    iStopProof. revert n. induction l;intros n;iIntros "[#[H Hintro] (Hn & Hω & HH)]".
    - simpl. rewrite fupd_trans.
      iMod ("H" with "HH Hω") as "[>Hω >HH]". auto.
    - iDestruct (@fupd_unfold_implies Σ Ω Hws C noTransInG0 ω with "H") as "#H'".
      simpl. rewrite /= -Nat.add_succ_r.
      iDestruct "Hn" as "[Hone [Hm Hn]]".
      rewrite (fupd_trans ⊤ ⊤).
      iApply bupd_elim.
      iMod ("H" with "HH Hω") as "[>Hω >HH]".
      iModIntro.
      iAssert (|={∅}▷=>^(S $ num_laters_per_step n) |={∅,⊤}=> ⚡={transmap_insert_inG (f a) Ω}=> ⚡={[l]}▷=>^(S n) |={⊤,∅}=> P)%I with "HH" as "HH".
      iDestruct ("H'" with "HH Hω") as "HH".
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
      iApply bupd_elim.
      iMod ("H" with "HP Hω") as "[>Hω >HP]".
      iModIntro.
      iApply (transmap_plain (transmap_insert_inG (f a) Ω)).
      iAssert (⚡={transmap_insert_inG (f a) Ω}=> ω ⊤)%I with "[Hω]" as "HA1".
      { iApply "Hintro". iFrame. }
      iModIntro.
      iDestruct (IHl with "[$H $HA1 $Hn $HP $Hintro]") as "HH";auto.
  Qed.

  Lemma fupdN_lc_elim `{!invGIndS_gen HasLc Σ Ω} E1 P n :
    (wsat ∗ ownE E1 ∗ £ (3 * n) ∗ |={E1}▷=>^n P) ⊢ le_upd.le_upd (wsat ∗ ownE E1 ∗ P).
  Proof.
    induction n.
    - simpl. iIntros "(Hwsat & HE & Hlc & HP)". iModIntro. iFrame.
    - rewrite -mult_n_Sm.
      rewrite lc_split. iIntros "[Hwsat [HE [[Hn Hlc] HP]]]".
      remember (3 * n) as m.
      simpl. rewrite {1}fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
      iMod ("HP" with "[$]") as "HP".
      iPoseProof (except_0_into_later with "HP") as "HP".
      iDestruct "Hlc" as "(Hone & Hone1 & Hone2)".
      iApply (le_upd.le_upd_later_elim with "Hone"). iNext.
      iDestruct "HP" as "(Hwsat & HE & HP)".
      iApply (le_upd.le_upd_later_elim with "Hone1"). iNext.
      rewrite {1}fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
      iMod ("HP" with "[$]") as "HP".
      iPoseProof (except_0_into_later with "HP") as "HP".
      iApply (le_upd.le_upd_later_elim with "Hone2"). iNext.
      iDestruct "HP" as "(Hwsat & HE & HP)".
      iApply IHn. iFrame.
  Qed.

  Lemma fupd_lc_elim `{!invGIndS_gen HasLc Σ Ω} E1 E2 P :
    (wsat ∗ ownE E1 ∗ £ 1 ∗ |={E1,E2}=> P) ⊢ le_upd.le_upd (wsat ∗ ownE E2 ∗ P).
  Proof.
    iIntros "[Hwsat [HE [Hone HP]]]".
    rewrite {1}fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
    iMod ("HP" with "[$]") as "HP".
    iPoseProof (except_0_into_later with "HP") as "HP".
    iApply (le_upd.le_upd_later_elim with "Hone"). iNext.
    iFrame. done.
  Qed.    

  
  Lemma step_fupdN_nextgen_soundness_lc (l : list A) :
    invGIndpreS Σ Ω → ∀ P : iProp Σ,
        Plain P → ∀ (n m : nat), (∀ (Hinv : invGIndS_gen HasLc Σ Ω), £ m ={⊤}=∗ ⚡={[l]}▷=>^(n) |={⊤,∅}=> P) → (⊢ P)%stdpp.
  Proof.
    intros until P. inversion H0. intros HPlain n m Hiter.
    (* apply (lc_soundness (m + 2 + steps_sum (λ n, 4 + 3 * num_laters_per_step n) n (length l)));[auto|]. *)
    (* intros Hc. iIntros "Hlc". *)
    apply (laterN_soundness _ ((m + 3 + steps_sum (λ n0 : nat, 4 + 3 * num_laters_per_step n0) n (length l)) * S (S (length l)))).
    iMod wsat_alloc as (Hw) "[Hw HE]".
    iMod (lc_alloc (m + 2 + steps_sum (λ n, 4 + 3 * num_laters_per_step n) n (length l))) as (Hc) "[Hsuppl Hlc]".
    set (Hinv := InvIndG HasLc _ Ω Hw Hc).
    specialize (Hiter Hinv).
    rewrite !lc_split. iDestruct "Hlc" as "[[Hm Hone] Hms]".
    iDestruct (Hiter with "Hm") as "HH". clear Hiter.
    iDestruct "Hone" as "[Hone1 Hone2]".
    iDestruct (fupd_lc_elim with "[$HH $Hw $HE $Hone1]") as "Hres".
    iDestruct (le_upd.le_upd_elim with "Hsuppl Hres") as "HH".
    rewrite -mult_n_Sm. rewrite {1}(Nat.add_comm ((m + 3 + steps_sum (λ n0 : nat, 4 + 3 * num_laters_per_step n0) n (length l)) * S (length l))).
    assert (m + 3 + steps_sum (λ n0 : nat, 4 + 3 * num_laters_per_step n0) n (length l) +
              (m + 3 + steps_sum (λ n0 : nat, 4 + 3 * num_laters_per_step n0) n (length l)) * S (length l)
            = m + 2 + steps_sum (λ n0 : nat, 4 + 3 * num_laters_per_step n0) n (length l) +
                (1 + (m + 3 + steps_sum (λ n0 : nat, 4 + 3 * num_laters_per_step n0) n (length l)) * S (length l))) as ->;[lia|].
    rewrite laterN_add.
    iApply bupd_laterN_plain.
    iApply (iter_modal_mono with "[-HH] HH").
    { intros. iIntros "J H". iMod "H". iIntros "!>!>".
      iApply "J". iFrame. }
    iIntros "HH". iApply bupd_elim. iMod "HH". rewrite (Nat.add_comm m 3).
    rewrite -Nat.add_assoc. (* iSimpl. *) iMod "HH" as (m0 Hm0) "[Hsupply [Hwsat [HE HP]]]".
    rewrite -(Nat.add_comm m 3). iModIntro.
    iStopProof. revert n m0 Hm0. induction l;intros n m0 Hm0;iIntros "[Hone [Hlc [Hsupply [Hwsat [HE HP]]]]]".
    - simpl in *.
      iDestruct (fupd_lc_elim with "[$HP $Hwsat $HE $Hone]") as "Hres".
      iDestruct (le_upd.le_upd_elim with "Hsupply Hres") as "HH".
      apply Nat.le_exists_sub in Hm0 as [p [Heq _]].
      assert ((m + 3 + 0) * 1 = S (m + 2)) as ->;[lia|]. rewrite Heq.
      rewrite -later_laterN. rewrite -Nat.add_1_r -Nat.add_1_r.
      rewrite -Nat.add_assoc (Nat.add_comm p m0) -Nat.add_assoc.
      rewrite laterN_add.
      iApply bupd_laterN_plain.
      iApply (iter_modal_mono with "[-HH] HH").
      { intros. iIntros "J H". iMod "H". iIntros "!>!>".
        iApply "J". iFrame. }
      iIntros "H". simpl. rewrite laterN_add /= -laterN_later /=.
      iApply bupd_elim. iMod "H" as ">H".
      iDestruct "H" as (m1 Hm1) "[Hsupply [? [? ?]]]".
      iModIntro. iNext. iNext. iNext. iFrame.
    - Abort.
      
    (* iStopProof. revert n. induction l;intros n;iIntros "[Hone [Hlc [Hwsat [HE HP]]]]". *)
    (* - simpl.  *)
    (*   iMod (fupd_lc_elim with "[$HP $Hwsat $HE $Hone]") as "[Hwsat [HE HP]]". *)
    (*   iModIntro. iFrame. *)
    (* - remember (λ n0 : nat, 4 + 3 * num_laters_per_step n0) as g. *)
    (*   simpl. *)
    (*   iMod (fupd_lc_elim with "[$HP $Hwsat $HE $Hone]") as "[Hwsat [HE HP]]". *)
    (*   rewrite lc_succ lc_split. *)
    (*   iDestruct "Hlc" as "[Hone [Hlcs Hrest]]". *)
    (*   remember (steps_sum g (S n) (length l)) as m. *)
    (*   subst g. iDestruct "Hlcs" as "((Hone1 & Hone2 & Hone3 & Hone4) & Hlc)". *)
    (*   iMod (fupd_lc_elim with "[$HP $Hwsat $HE $Hone]") as "[Hwsat [HE HP]]". *)
    (*   iApply (le_upd.le_upd_later_elim with "Hone1"). iNext. *)
    (*   iMod (fupd_lc_elim with "[$HP $Hwsat $HE $Hone2]") as "[Hwsat [HE HP]]". *)
    (*   iMod (fupdN_lc_elim with "[$Hwsat $HP $HE $Hlc]") as "[Hwsat [HE HP]]". *)
    (*   iMod (fupd_lc_elim with "[$HP $Hwsat $HE $Hone3]") as "[Hwsat [HE HP]]". *)
    (*   iModIntro. *)
    (*   iApply (transmap_plain (transmap_insert_inG (f a) Ω)). *)
    (*   iDestruct (wsat_ind_insert_intro (f a) with "Hwsat") as "Hwsat". *)
    (*   iDestruct (ownE_ind_insert_intro _ (f a) with "HE") as "HE". *)
    (*   iModIntro. rewrite Heqm. *)
    (*   iDestruct (IHl with "[$Hone4 $Hrest $Hwsat $HE $HP]") as "HH". *)
    

End bnextgen_n_open_soundness.
