From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants fancy_updates wsat later_credits.
From iris.prelude Require Import options.

From nextgen Require Import cmra_morphism_extra.
From nextgen Require Export nextgen_basic.
Import uPred.


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

(* Section bnextgen_pred_imod. *)
(*   Context {M : ucmra} {A : Type} (f : A -> M → M) `{!forall a, CmraMorphism (f a)} {num_laters_per_step : nat -> nat} *)
(*     `{BiFUpd (uPredI M)}. *)
  
(*   Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope. *)
(*   Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q). *)
(*   Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope. *)
  
(*   Local Arguments uPred_holds {_} !_ _ _ /. *)

(*   Ltac unseal := try uPred.unseal; rewrite !uPred_bnextgen_unseal !/uPred_holds /=. *)

(*   Fixpoint bnextgen_n *)
(*     (l : list A) (start : nat) (P : uPredI M) : uPredI M := *)
(*     match l with *)
(*     | [] => P *)
(*     | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) |={∅,⊤}=> *)
(*         ⚡={f a}=> (bnextgen_n l' (S start) P) *)
(*     end. *)
  
(*   Fixpoint bnextgen_n_open *)
(*     (l : list A) (start : nat) (P : uPredI M) : uPredI M := *)
(*     match l with *)
(*     | [] =>  |={⊤,∅}=> P *)
(*     | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) *)
(*                           ⚡={f a}=> (bnextgen_n_open l' (S start) P) *)
(*     end. *)

(*   Notation "⚡={[ l ]}▷=>^ ( n ) P" := (bnextgen_n l n P) *)
(*          (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope. *)

(*   Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (bnextgen_n_open l n P) *)
(*          (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope. *)

 
(*   Lemma bnextgen_n_mono P Q l n : *)
(*     (P ⊢ Q) → (⚡={[ l ]}▷=>^(n) P) ⊢ (⚡={[ l ]}▷=>^(n) Q). *)
(*   Proof. *)
(*     intros Hi. revert n; induction l =>n;auto. *)
(*     iIntros "H". simpl. *)
(*     iMod "H". iModIntro. *)
(*     iApply (step_fupdN_mono with "H"). iIntros "H". *)
(*     iMod "H". iModIntro. iApply (bnextgen_mono with "H"). iApply IHl. *)
(*   Qed. *)

(*   (* Lemma bnextgen_n_mono_keep P Q l n : *) *)
(*   (*   ((|={⊤}=> P) ⊢ |={⊤}=> Q) → (⚡={[ l ]}▷=>^(n) P) ⊢ (⚡={[ l ]}▷=>^(n) Q). *) *)
(*   (* Proof. *) *)
(*   (*   intros Hi. revert n; induction l =>n;auto. *) *)
(*   (*   { simpl. } *) *)
(*   (*   iIntros "H". simpl. *) *)
(*   (*   iMod "H". iModIntro. *) *)
(*   (*   iApply (step_fupdN_mono with "H"). iIntros "H". *) *)
(*   (*   iMod "H". iModIntro. iApply (bnextgen_mono with "H"). iApply IHl. *) *)
(*   (* Qed. *) *)

(*   Global Instance bnextgen_n_mono' l n : *)
(*     Proper ((⊢) ==> (⊢)) (bnextgen_n l n). *)
(*   Proof. intros P Q. apply bnextgen_n_mono. Qed. *)

(*   Global Instance nextgen_n_ne l n : NonExpansive (bnextgen_n l n). *)
(*   Proof. *)
(*     revert n; induction l =>n;simpl;auto;try apply _. *)
(*     (* { apply fupd_ne. } *) *)
(*     intros x P Q Hne. *)
(*     destruct H with a. simpl in *. *)
(*     apply fupd_ne. *)
(*     apply fupd_ne,later_ne, fupd_ne. *)
(*     apply step_fupdN_ne. apply fupd_ne. *)
(*     apply bnextgen_ne.  apply IHl. auto. *)
(*   Qed. *)

(*   Global Instance bnextgen_n_proper l n : *)
(*     Proper ((≡) ==> (≡)) (bnextgen_n l n) := ne_proper _. *)

(*   Lemma bnextgen_n_open_snoc l x n P : *)
(*     (⚡={[(l ++ [x])]}▷=>>^(n) P) ⊣⊢ ⚡={[l]}▷=>>^(n) (|={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) ⚡={f x}=> |={⊤,∅}=> P). *)
(*   Proof. *)
(*     revert n; induction l => n. *)
(*     - simpl. iSplit; iIntros "H"; rewrite Nat.add_0_r; auto. *)
(*     - simpl. iSplit;iIntros ">H". *)
(*       all: iModIntro. *)
(*       all: iApply (step_fupdN_mono with "H"); iIntros "H". *)
(*       all: iApply (bnextgen_mono with "H"); iIntros "H". *)
(*       + iDestruct (IHl with "H") as "H". *)
(*         rewrite Nat.add_succ_r. iFrame. *)
(*       + iApply IHl. rewrite Nat.add_succ_r. iFrame. *)
(*   Qed. *)

(*   Lemma bnextgen_n_snoc l x n P : *)
(*     (⚡={[(l ++ [x])]}▷=>^(n) P) ⊣⊢ ⚡={[l]}▷=>^(n) (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) |={∅,⊤}=> ⚡={f x}=> P). *)
(*   Proof. *)
(*     revert n; induction l => n. *)
(*     - simpl. iSplit; iIntros "H"; rewrite Nat.add_0_r; auto. (* rewrite fupd_trans. auto. *) *)
(*     - simpl. iSplit;iIntros ">H". *)
(*       all: iModIntro. *)
(*       all: iApply (step_fupdN_mono with "H"); iIntros "H". *)
(*       all: iApply (bnextgen_mono with "H"); iIntros "H". *)
(*       + iDestruct (IHl with "H") as "H". *)
(*         rewrite Nat.add_succ_r. iFrame. *)
(*       + iApply IHl. rewrite Nat.add_succ_r. iFrame. *)
(*   Qed. *)

(*   Lemma bnextgen_n_mono_open_keep  P Q l n : *)
(*     ((|={⊤,∅}=> P) ⊢ |={⊤,∅}=> Q) → (⚡={[ l ]}▷=>>^(n) P) ⊢ (⚡={[ l ]}▷=>>^(n) Q). *)
(*   Proof. *)
(*     intros Hi. revert n; induction l =>n;auto. *)
(*     iIntros "H". simpl. *)
(*     iMod "H". iModIntro. *)
(*     iApply (step_fupdN_mono with "H"). iIntros "H". *)
(*     iApply (bnextgen_mono with "H"). iApply IHl. *)
(*   Qed. *)

(*   Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat := *)
(*   match ns with *)
(*   | O => 0 *)
(*   | S ns => *)
(*       S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns *)
(*   end. *)


(*   Fixpoint foo *)
(*     (l : list A) (start : nat) (P : uPredI M) : uPredI M := *)
(*     match l with *)
(*     | [] => P *)
(*     | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) *)
(*                           (foo l' (S start) P) *)
(*     end. *)

(*   Lemma foo_snoc l x n P : *)
(*     foo (l ++ [x]) n P -∗ foo (l) n (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) P). *)
(*   Proof. *)
(*     revert n; induction l => n. *)
(*     - simpl. iIntros "H". rewrite Nat.add_0_r. auto. *)
(*     - simpl. iIntros ">H". *)
(*       iModIntro. *)
(*       iApply (step_fupdN_mono with "H"). iIntros "H". *)
(*       rewrite -PeanoNat.Nat.add_succ_comm. iApply IHl. auto. *)
(*   Qed. *)

(*   Lemma foo_snoc_inv l x n P : *)
(*     foo (l) n (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) P) ⊣⊢ foo (l ++ [x]) n P. *)
(*   Proof. *)
(*     revert n; induction l => n. *)
(*     - simpl. iSplit; iIntros "H"; rewrite Nat.add_0_r; auto. *)
(*     - simpl. iSplit; iIntros ">H". *)
(*       all: iModIntro. *)
(*       all: iApply (step_fupdN_mono with "H"); iIntros "H". *)
(*       all: rewrite -PeanoNat.Nat.add_succ_comm; iApply IHl; auto. *)
(*   Qed. *)

(*   (* Lemma  *) *)

(*   (* Lemma test P `{!Plain P} (* `{!Absorbing P} *) (* `{BiPlainly (uPredI M)} *) l ns : *) *)
(*   (*   foo l ns P -∗ (⚡={[l]}▷=>>^(ns) P). *) *)
(*   (* Proof. *) *)
(*   (*   revert ns; induction l using rev_ind; intros ns. *) *)
(*   (*   - simpl. auto. *) *)
(*   (*   - iIntros "H". rewrite -foo_snoc_inv. *) *)
(*   (*     rewrite bnextgen_n_snoc. *) *)
(*   (*     iDestruct (bnextgen_n_snoc with "H") as "H". iIntros "H". *) *)
      
(*   (*     iApply IHl. *) *)
      
      
    

(* End bnextgen_pred_imod. *)

(* Section test. *)
(*   Context {A : Type} {Σ : gFunctors} (f : A -> iResUR Σ → iResUR Σ) `{!forall a, CmraMorphism (f a)} *)
(*     {num_laters_per_step : nat -> nat}. *)

(*   Notation "⚡={[ l ]}▷=>^ ( n ) P" := (@bnextgen_n _ _ f _ num_laters_per_step _ l n P) *)
(*          (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope. *)

(*   Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (@bnextgen_n_open _ _ f _ num_laters_per_step _ l n P) *)
(*          (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope. *)

(*   Lemma step_fupdN_soundness_no_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m : *)
(*     (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) → *)
(*     ⊢ P. *)
(*   Proof. *)
(*     intros Hiter. *)
(*     apply (laterN_soundness _  (S n)); simpl. *)
(*     apply (fupd_soundness_no_lc ⊤ ⊤ _ m)=> Hinv. iIntros "Hc". *)
(*     iPoseProof (Hiter Hinv) as "H". clear Hiter. *)
(*     iApply fupd_plainly_mask_empty. iSpecialize ("H" with "Hc"). *)
(*     iMod (step_fupdN_plain with "H") as "H". iMod "H". iModIntro. *)
(*     rewrite -later_plainly -laterN_plainly -later_laterN laterN_later. *)
(*     iNext. iMod "H" as "#H". auto. *)
(*   Qed. *)

(*   (* Lemma step_fupdN_nextgen_soundness_gen : *) *)
(*   (*   invGpreS Σ → ∀ P : iProp Σ, *) *)
(*   (*       Plain P → ∀ (hlc : has_lc) (n m : nat), (∀ (Hinv : invGS_gen hlc Σ) l, £ m ={⊤}=∗ ⚡={[l]}▷=>>^(n) P) → (⊢ P)%stdpp. *) *)
(*   (* Proof. *) *)
(*   (*   intros. *) *)
(*   (*   eapply (fupd_soundness_gen _ hlc m ⊤ ⊤);eauto. *) *)
(*   (*   intros. specialize H2 with Hinv []. simpl in *. auto. *) *)
(*   (* Qed. *) *)


(*   Lemma test : *)
(*     invGpreS Σ *)
(*     → ∀ P : iProp Σ, Plain P → ∀ (n m : nat) l, (∀ Hinv : invGS_gen HasNoLc Σ, *)
(*                                                   £ m ={⊤}=∗ ⚡={[ l ]}▷=>^(n) P) → (⊢ P)%stdpp. *)
(*   Proof. *)
(*     intros. (* apply bupd_soundness;auto. *) *)
(*     pose proof (step_fupdN_soundness_no_lc P). *)

    
(*     eapply (step_fupdN_soundness_gen _ HasNoLc ((length l)) m);eauto. *)
(*     intros. iIntros "Hm". *)
(*     iDestruct (H2 with "Hm") as "H". clear H2. *)
(*     iRevert "H". iApply entails_wand. *)
(*     revert n. induction l. *)
(*     - simpl. iIntros (n) "H". iMod "H". *)
(*       iApply fupd_mask_intro;auto. (* iIntros "Hcls". *) *)
(*       (* iApply step_fupdN_intro;auto. *) *)
(*     - simpl. intros. iIntros "H". *)
      
      

(*       iAssert (|={⊤}=> |={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step n) |={∅,⊤}=> ⚡={f a}=> |={⊤,∅}=> |={∅}▷=>^(length l) P)%I with "[H]" as  "H". *)
(*       { iMod "H". iModIntro. iMod "H". iModIntro. *)
(*         iApply (step_fupdN_mono with "H"). *)
(*         iIntros "H". *)
(*         iMod "H". iModIntro. iModIntro. *)
(*         iApply IHl. auto. } *)
      
      
      
(*       iApply IHl. *)

      

(*       intros. auto. *)
(*     - simpl. intros. iIntros "H". *)
(*       iAssert (|={⊤}=> |={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step n) P)%I with "[H]" as "H". *)
(*       { iMod "H". iMod "H". *)
(*         pose proof fupd_soundness_gen. *)

(*         iModIntro. iApply (step_fupdN_mono with "H"). iIntros "H". *)
(*         iApply bnextgen_plain. iApply (bnextgen_mono with "H"). *)
(*         iIntros "H". iApply IHl *)
        
(*       }  *)
      
(*       iMod "H". iMod "H". *)
(*       iApply fupd_mask_intro_discard. *)


    
(*     intros. *)
(*     eapply fancy_updates.step_fupdN_soundness_no_lc with (* (hlc := HasNoLc) *) (m:=m) (n := (length l));eauto. *)
(*     intros. specialize (H2 Hinv). *)
(*     iIntros "Hm". iDestruct (H2 with "Hm") as "H". *)
(*     clear H2. (* rewrite step_fupdN_S_fupd.  *)iRevert "H". iApply entails_wand. *)
(*     revert n Hinv. induction l using rev_ind =>n Hinv. *)
(*     - simpl. iIntros "Hp". iMod "Hp". *)
(*       iApply fupd_mask_intro;auto. *)
(*       (* iIntros "Hcls". iNext. iMod "Hcls". iModIntro. auto. *) *)
(*     - iIntros "H". rewrite app_length /=. (* rewrite -Nat.add_succ_l. (* simpl. *) *) *)
(*       (* rewrite PeanoNat.Nat.add_1_r. rewrite bnextgen_n_snoc. simpl. *) *)
(*       rewrite step_fupdN_add. rewrite bnextgen_n_snoc. destruct l. *)

(*       iApply step_fupdN_mono. *)
      
(*       iApply fupd_mask_intro;auto. iIntros "Hcls". iNext. *)

(*       rewrite PeanoNat.Nat.add_1_r. rewrite bnextgen_n_snoc. *)
(*       iMod "Hcls". *)
(*       iModIntro. rewrite PeanoNat.Nat.add_1_r. iApply IHl. *)
(*       rewrite step_fupdN_add /=. *)
(*       rewrite bnextgen_n_snoc. *)

(*       iAssert ((|={⊤,∅}=> |={∅}▷=>^(length l) P) -∗ *)
(*                                                    |={⊤,∅}=> |={∅}▷=>^(length l) |={∅}▷=> P)%I as "tes". *)
(*       { iIntros "H". iMod "H". iModIntro. iApply (step_fupdN_mono with "H"). iIntros "H". *)
(*         iModIntro. iNext. iModIntro. auto. } *)
(*       iApply "tes". *)
      
(*       iApply (IHl n). iMod "H". iModIntro. *)
(*       iApply (bnextgen_n_mono with "H"). iIntros "H". *)

(*       iAssert (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step (n + length l)) |={∅,⊤}=> P)%I with "[H]" as "H". *)
(*       { iMod "H". iModIntro. iApply (step_fupdN_mono with "H"). iIntros "H". iMod "H". *)
(*         iModIntro. iApply (bnextgen_plain). eauto. } *)

(*       unseal. simpl. *)
      
(*       simpl in IHl. *)
(*       iApply IHl. *)

    
(*     intros. (* apply bupd_soundness;auto. *) *)
(*     eapply (fupd_soundness_gen _ HasNoLc m ⊤ ⊤);eauto. *)
(*     intros. iIntros "Hm". *)
(*     iDestruct (H2 with "Hm") as "H". clear H2. *)
(*     iRevert "H". iApply entails_wand. *)
(*     revert n. induction l. *)
(*     - simpl. intros. auto. *)
(*     - simpl. intros. iIntros "H". *)
(*       iAssert (|={⊤}=> |={⊤,∅}=> |={∅}▷=> |={∅}▷=>^(num_laters_per_step n) P)%I with "[H]" as "H". *)
(*       { iMod "H". iMod "H". *)
(*         pose proof fupd_soundness_gen. *)

(*         iModIntro. iApply (step_fupdN_mono with "H"). iIntros "H". *)
(*         iApply bnextgen_plain. iApply (bnextgen_mono with "H"). *)
(*         iIntros "H". iApply IHl *)
        
(*       }  *)
      
(*       iMod "H". iMod "H". *)
(*       iApply fupd_mask_intro_discard. *)
    

(*   Lemma step_fupdN_nextgen_soundness_gen : *)
(*     invGpreS Σ → ∀ P : iProp Σ, *)
(*         Plain P → ∀ (hlc : has_lc) (n m : nat), (∀ (Hinv : invGS_gen hlc Σ) l, £ m -∗ ⚡={[l]}▷=>>^(n) P) → (⊢ P)%stdpp. *)
(*   Proof. *)
(*     intros. *)
(*     eapply (fupd_soundness_gen _ hlc m ⊤ ⊤);eauto. *)
(*     intros. specialize H2 with Hinv []. simpl in *. auto. *)
(*   Qed. *)

  

(*   Lemma step_fupdN_nextgen_soundness_gen' : *)
(*     invGpreS Σ → ∀ P : iProp Σ, *)
(*         Plain P → ∀ l (hlc : has_lc) (n m : nat), (∀ (Hinv : invGS_gen hlc Σ), £ m -∗ ⚡={[l]}▷=>>^(n) P) → (⊢ P)%stdpp. *)
(*   Proof. *)
(*     (* induction l;intros. *) *)
(*     (* - simpl. eapply (fupd_soundness_gen _ hlc m ⊤ ⊤);eauto. *) *)
(*     (* - simpl in *. eapply IHl. intros. *) *)
(*     (*   iIntros "Hm". iDestruct (H2 with "Hm") as "H". *) *)
(*     (*   apply H2. ;eauto. apply H2. *) *)

(*     intros. *)
(*     eapply (fupd_soundness_gen _ hlc m ⊤ ⊤);eauto. *)
(*     intros. specialize H2 with Hinv. *)
(*     iIntros "Hm". iDestruct (H2 with "Hm") as "H". *)
(*     iRevert "H". iApply wand_entails. *)
(*     clear H2. revert n. induction l;intros. *)
(*     - simpl in *. iIntros ">H". auto. *)
(*     - simpl. iIntros "H". iApply (IHl (S n)). *)

(*       lc_fupd_elim_later *)


    
(*     revert n. induction l using rev_ind;intros. *)
(*     - simpl in *. iIntros ">H". auto. (* eapply fupd_soundness_gen;eauto. *) *)
(*     - apply (laterN_soundness _  (S 0)); simpl. iIntros "H". iDestruct (bnextgen_n_snoc with "H") as "H". *)
(*       iApply IHl. iApply (bnextgen_n_mono_open_keep with "H"). *)
(*       iIntros "H". iMod "H". iApply fupd_plainly_mask_empty. *)
(*       iMod "H". iMod "H". rewrite -later_plainly.  -laterN_plainly -later_laterN laterN_later. *)

(*       iModIntro. iApply fupd_mask_intro. iModIntro. *)

(*       apply IHl. intros. specialize H2 with Hinv. *)
(*       iIntros "Hm". iDestruct (H2 with "Hm") as "H". *)
(*       iDestruct (bnextgen_n_snoc with "H") as "H". *)
(*       iApply (bnextgen_n_mono_open_keep with "H"). *)
(*       iIntros "H". iMod "H". iModIntro. *)
      
      
    

(* End test. *)
