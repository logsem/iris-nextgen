From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From nextgen.case_study.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
From nextgen Require Export nextgen_soundness.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First *)
(* we prove a number of auxilary results. *)

(* Global Instance step_fupdN_ne *)
(*   (PROP : bi) (BiFUpd0 : BiFUpd PROP) (Eo Ei : coPset) (n : nat) : (NonExpansive (λ (P : PROP), |={Eo}[Ei]▷=>^n P))%I. *)
(* Proof. *)
(*   induction n;simpl;try apply _. *)
(*   intros m P1 P2 Hm. apply fupd_ne, later_ne, fupd_ne, IHn =>//. *)
(* Qed. *)

(* Lemma bnextgen_n_soundness (Σ : gFunctors) (invGpreS0 : invGpreS Σ) (P : iProp Σ) (Plain0 : Plain P) (hlc : has_lc) (n m : nat) : *)
(*   (∀ Hinv : invGS_gen hlc Σ, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) → ⊢ P. *)

(* Fixpoint nextgen_n `{!irisGS_gen hlc Λ Σ} *)
(*   (l : list (expr Λ)) (start : nat) (P : iProp Σ) : iProp Σ := *)
(*   match l with *)
(*   | [] => |={⊤}=> P *)
(*   | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) |={∅,⊤}=> ⚡={next_state a}=> (nextgen_n l' (S start) P) *)
(*   end. *)

(* Fixpoint nextgen_n_open `{!irisGS_gen hlc Λ Σ} *)
(*   (l : list (expr Λ)) (start : nat) (P : iProp Σ) : iProp Σ := *)
(*   match l with *)
(*   | [] => P *)
(*   | a :: l' => |={∅}▷=>^(S $ num_laters_per_step start) ⚡={next_state a}=> (nextgen_n_open l' (S start) P) *)
(*   end. *)

(* Notation "⚡={[ l ]}▷=>^ ( n ) P" := (nextgen_n l n P) *)
(*                                        (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope. *)

(* Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (nextgen_n_open l n P) *)
(*                                         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope. *)

Section adequacy.
Context `{!irisGS_gen HasNoLc Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

(* Fixpoint nextgen_n *)
(*   (l : list (expr Λ)) (start : nat) (P : iProp Σ) : iProp Σ := *)
(*   match l with *)
(*   | [] => |={⊤}=> P *)
(*   | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) |={∅,⊤}=> ⚡={next_state a}=> (nextgen_n l' (S start) P) *)
(*   end. *)

(* Fixpoint nextgen_n_open {irisGS_gen0 : invGS_gen hlc Σ} *)
(*   (l : list (expr Λ)) (start : nat) (P : iProp Σ) : iProp Σ := *)
(*   match l with *)
(*   | [] => |={⊤}=> P *)
(*   | a :: l' => |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step start) ⚡={next_state a}=> (nextgen_n_open l' (S start) P) *)
(*   end. *)

(* Notation "⚡={[ l ]}▷=>^ ( n ) P" := (nextgen_n l n P) *)
(*                                        (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope. *)

(* Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (nextgen_n_open l n P) *)
(*                                         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope. *)
  
  

Notation "⚡={[ l ]}▷=>^ ( n ) P" := (@bnextgen_n _ _ (next_state) _ num_laters_per_step _ l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>^ ( n )  P") : bi_scope.

Notation "⚡={[ l ]}▷=>>^ ( n ) P" := (@bnextgen_n_open _ _ (next_state) _ num_laters_per_step _ l n P)
         (at level 99, l at level 50, n at level 50, P at level 200, format "⚡={[ l ]}▷=>>^ ( n )  P") : bi_scope.

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.


Inductive step_single_thread (e1 : expr Λ) (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
| step_atomic σ1 e2 σ2 :
  ρ1 = ([e1], σ1) →
  ρ2 = ([e2], σ2) →
  prim_step e1 σ1 κ e2 σ2 [] →
  step_single_thread e1 ρ1 κ ρ2.
Local Hint Constructors step : core.

Inductive nsteps_single_thread : (list (expr Λ)) -> nat → cfg Λ → list (observation Λ) → cfg Λ → Prop :=
| nsteps_refl ρ :
  nsteps_single_thread [] 0 ρ [] ρ
| nsteps_l e1 es1 n ρ1 ρ2 ρ3 κ κs :
  (* ess !! i = Some es1 -> *)
  step_single_thread e1 ρ1 κ ρ2 →
  nsteps_single_thread es1 n ρ2 κs ρ3 →
  nsteps_single_thread (e1 :: es1) (S n) ρ1 (κ ++ κs) ρ3.
Local Hint Constructors nsteps : core.

Lemma zip_length {A B : Type} (l1 : list A) (l2 : list B) :
  length (zip l1 l2) = length l1 `min` length l2.
Proof.
  revert l2; induction l1; intros l2; auto.
  simpl. induction l2;simpl;auto.
Qed.

Lemma zip_app {A B : Type} (l1 l1' : list A) (l2 l2' : list B) :
  length l1 = length l2 ->
  zip (l1 ++ l1') (l2 ++ l2') = (zip l1 l2) ++ zip l1' l2'.
Proof.
  revert l2; induction l1; intros l2 Hlen.
  - destruct l2;done.
  - destruct l2;[done|].
    inversion Hlen.
    simpl. rewrite IHl1//.
Qed.

Lemma alter_replicate {A : Type} (a : A) (n : nat) (i : nat) (f : A -> A) :
  i < n ->
  alter f i (replicate n a) = replicate (i) a ++ f a :: replicate (n - i - 1) a.
Proof.
  revert i; induction n;intros i;simpl.
  - intros Hi. lia.
  - intros Hi. destruct i.
    + rewrite /= Nat.sub_0_r. auto.
    + simpl. apply Arith_prebase.lt_S_n in Hi.
      apply IHn in Hi as Hi'. simpl.
      unfold alter in Hi'. rewrite Hi'.
      rewrite app_comm_cons -replicate_S.
      auto.
Qed.

Local Lemma wp_step s e1 σ1 ns κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 ns (κ ++ κs) nt -∗
  £ (S (num_laters_per_step ns)) -∗
  WP e1 @ s; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
  (⚡={next_state e1}=> state_interp σ2 (S ns) κs (nt + length efs)) ∗ (⚡={next_state e1}=> WP e2 @ s; ⊤ {{ Φ }}).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ Hcred H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 ns with "Hσ") as "(_ & H)". iModIntro.
  iApply (step_fupdN_wand with "(H [//] Hcred)"). iIntros ">(H1 & H2 & H3)".
  iFrame. rewrite Nat.add_comm. auto.
Qed.

Lemma nsteps_single_thread_length es' n ρ1 ρ2 κs :
  nsteps_single_thread es' n ρ1 κs ρ2 →
  length es' = n.
Proof.
  revert es' ρ1 ρ2 κs. induction n; intros es' ρ1 ρ2 κs.
  - intros Hstep. inversion Hstep;auto.
  - intros Hstep. inversion Hstep;simpl.
    erewrite IHn;eauto.
Qed.

Local Lemma wptp_preservation s n es' es1 es2 κs κs' σ1 ns σ2 Φ nt :
  nsteps_single_thread es' n (es1, σ1) κs (es2, σ2) →
  £ (steps_sum num_laters_per_step ns n) -∗
  wptp s es1 [Φ] -∗
  (state_interp σ1 ns (κs ++ κs') nt) -∗
  ⚡={[es']}▷=>^(ns) ∃ nt', state_interp σ2 (n + ns) κs' (nt + nt') ∗
  wptp s es2 [Φ].
Proof.
  revert nt es' es1 es2 κs κs' σ1 ns σ2 Φ.
  induction n as [|n IH]=> nt es' es1 es2 κs κs' σ1 ns σ2 Φ /=.
  { inversion_clear 1; iIntros "? ? ?". simpl. iExists 0.
    rewrite Nat.add_0_r. iFrame. }
  iIntros (Hsteps) "Hcred He Hσ ". inversion_clear Hsteps as [|???? [t1' σ1']].
  rewrite -(assoc_L (++)) -{1}plus_Sn_m plus_n_Sm.
  inversion H;simplify_eq. rewrite lc_split. iDestruct "Hcred" as "[Hc1 Hc2]".
  simpl.
  iDestruct "He" as "[He _]".
  iMod (wp_step with "Hσ Hc1 He") as "HH";first eauto.
  iApply step_fupdN_S_fupd. iModIntro. 
  iApply (step_fupdN_wand with "HH").
  iIntros "HH". iModIntro.
  iMod "HH". iModIntro. iDestruct "HH" as "[? H]".
  iAssert (⚡={next_state e1}=> £ (steps_sum num_laters_per_step (S ns) n))%I with "[Hc2]" as "Hc2";[admit|].
  iModIntro. rewrite /= Nat.add_0_r.
  iApply (IH with "[$] [H] [$]");first eauto.
  simpl. iFrame.
Admitted.

Local Lemma wp_not_stuck κs nt e σ ns Φ :
  state_interp σ ns κs nt -∗ WP e {{ Φ }} ={⊤, ∅}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?.
  { iMod (fupd_mask_subseteq ∅); first set_solver. iModIntro. eauto. }
  iSpecialize ("H" $! σ ns [] κs with "Hσ"). rewrite sep_elim_l.
  iMod "H" as "%". iModIntro. eauto.
Qed.

(** The adequacy statement of Iris consists of two parts: *)
(*       (1) the postcondition for all threads that have terminated in values *)
(*       and (2) progress (i.e., after n steps the program is not stuck). *)
(*     For an n-step execution of a thread pool, the two parts are given by *)
(*     [wptp_strong_adequacy] and [wptp_progress] below. *)

(*     For the final adequacy theorem of Iris, [wp_strong_adequacy_gen], we would *)
(*     like to instantiate the Iris proof (i.e., instantiate the *)
(*     [∀ {Hinv : !invGS_gen hlc Σ} κs, ...]) and then use both lemmas to get *)
(*     progress and the postconditions. Unfortunately, since the addition of later *)
(*     credits, this is no longer possible, because the original proof relied on an *)
(*     interaction of the update modality and plain propositions. So instead, we *)
(*     employ a trick: we duplicate the instantiation of the Iris proof, such *)
(*     that we can "run the WP proof twice". That is, we instantiate the *)
(*     [∀ {Hinv : !invGS_gen hlc Σ} κs, ...] both in [wp_progress_gen] and *)
(*     [wp_strong_adequacy_gen]. In doing  so, we can avoid the interactions with *)
(*     the plain modality. In [wp_strong_adequacy_gen], we can then make use of *)
(*     [wp_progress_gen] to prove the progress component of the main adequacy theorem. *)
(* *)

Local Lemma wptp_postconditions Φ es' κs' s n es1 es2 κs σ1 ns σ2 nt:
  nsteps_single_thread es' n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  wptp s es1 [λ v, |={⊤}=> Φ v] -∗
  ⚡={[es']}▷=>^(ns) ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;[λ v, |={⊤}=> Φ v], from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "Hσ Hcred He". iDestruct (wptp_preservation with "Hcred He Hσ") as "Hwp"; first done.
  iApply (bnextgen_n_mono with "Hwp").
  iDestruct 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iExists _. iFrame "Hσ".
  (* iApply big_sepL2_fupd. *)
  iApply (big_sepL2_impl with "Ht").
  iIntros "!#" (? e Φ' ??) "Hwp".
  simplify_list_eq.
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl.
  iDestruct (wp_fupd with "Hwp") as "Hwp".
  by iApply wp_value_fupd'. 
Qed.


Local Lemma wptp_progress Φ es' κs' n es1 es2 κs σ1 ns σ2 nt e2 :
  nsteps_single_thread es' n (es1, σ1) κs (es2, σ2) →
  e2 ∈ es2 →
  state_interp σ1 ns (κs ++ κs') nt -∗
  £ (steps_sum num_laters_per_step ns n) -∗
  wptp NotStuck es1 [Φ] -∗
  ⚡={[es']}▷=>^(ns) |={⊤,∅}=> ⌜not_stuck e2 σ2⌝.
Proof.
  iIntros (Hstep Hel) "Hσ Hcred He". iDestruct (wptp_preservation with "Hcred He Hσ") as "Hwp"; first done.
  iApply (bnextgen_n_mono with "Hwp").
  iDestruct 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iDestruct (big_sepL2_length with "Ht") as %Hlen.
  destruct es2;try done. destruct es2;try done.
  apply elem_of_list_singleton in Hel. subst e.
  simpl. iDestruct "Ht" as "[Ht _]".
  iApply (wp_not_stuck with "Hσ Ht").
Qed.
End adequacy.

(* Lemma test `{!invGpreS Σ} {Λ} : *)
(*   ∀ P : iProp Σ, Plain P → ∀ (hlc : has_lc) (n m : nat), *)
(*       (∀ (Hinv : invGS_gen hlc Σ) l, £ m -∗ ⚡={[l]}▷=>^(n) P) → ⊢ P. *)
  

Local Lemma wp_progress_gen Σ Λ `{!invGpreS Σ} es σ1 n es' κs t2 σ2 e2
  (num_laters_per_step : nat → nat) (next_state : expr Λ -> iResUR Σ -> iResUR Σ)
  (next_state_ne : ∀ e : expr Λ, CmraMorphism (next_state e)) :
    (∀ `{Hinv : !invGS_gen hlc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ)
         state_interp_mono,
       let _ : irisGS_gen hlc Λ Σ := IrisG Hinv stateI fork_post next_state next_state_ne num_laters_per_step
                                  state_interp_mono
       in
       stateI σ1 0 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ ⊤ {{ Φ }})) →
  nsteps_single_thread es' n (es, σ1) κs (t2, σ2) →
  e2 ∈ t2 →
  not_stuck e2 σ2.
Proof.
  intros Hwp ??.
  pose proof (@step_fupdN_nextgen_soundness_no_lc (expr Λ) Σ next_state _ num_laters_per_step es' _ (⌜not_stuck e2 σ2⌝)%I _ 0 (steps_sum num_laters_per_step 0 n)) as Hsound.
  eapply pure_soundness.
  apply Hsound.
  iIntros (Hinv) "Hn".
  destruct n.
  { inversion H;subst. simpl. auto. }
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp)".

  iDestruct (wptp_progress) as "HH";[apply H|apply H0|..].


(*
  iDestruct Hwp as (stateI Φ fork_post state_interp_mono) "HH". "(Hσ & Hwp)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_progress _ _ _
       (IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hcred  Hwp") as "H"; [done| done |by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜not_stuck e2 σ2⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H"). iIntros "$".
Qed.
  

  apply 
  
  eapply (step_fupdN_soundness_gen _ hlc (steps_sum num_laters_per_step 0 n)
    (steps_sum num_laters_per_step 0 n)).
  iIntros (Hinv) "Hcred".
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_progress _ _ _
       (IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hcred  Hwp") as "H"; [done| done |by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜not_stuck e2 σ2⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H"). iIntros "$".
Qed.

(** Iris's generic adequacy result *)
(** The lemma is parameterized by [use_credits] over whether to make later credits available or not. *)
(*   Below, a concrete instances is provided with later credits (see [wp_strong_adequacy]). *)
Lemma wp_strong_adequacy_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} s es σ1 n κs t2 σ2 φ
        (num_laters_per_step : nat → nat) :
  (* WP *)
  (∀ `{Hinv : !invGS_gen hlc Σ},
      ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ)
         (* Note: existentially quantifying over Iris goal! [iExists _] should *)
(*          usually work. *)
         state_interp_mono,
       let _ : irisGS_gen hlc Λ Σ := IrisG Hinv stateI fork_post num_laters_per_step
                                  state_interp_mono
       in
       stateI σ1 0 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all *)
(*          threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 n [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
         (* For all forked-off threads that are done, their postcondition *)
(*             [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we *)
(*          can conclude [φ] in the logic. After opening all required invariants, *)
(*          one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_gen _ hlc (steps_sum num_laters_per_step 0 n)
    (steps_sum num_laters_per_step 0 n)).
  iIntros (Hinv) "Hcred".
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_postconditions _ _ _
       (IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hcred Hwp") as "H"; [done|by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt') "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  rewrite -plus_n_O.
  iApply ("Hφ" with "[//] [%] [ ] Hσ Hes'");
    (* FIXME: Different implicit types for [length] are inferred, so [lia] and *)
(*     [congruence] do not work due to https://github.com/coq/coq/issues/16634 *)
    [by rewrite Hlen1 Hlen3| |]; last first.
  { by rewrite big_sepL2_replicate_r // big_sepL_omap. }
  (* At this point in the adequacy proof, we use a trick: we effectively run the *)
(*     user-provided WP proof again (i.e., instantiate the `invGS_gen` and execute the *)
(*     program) by using the lemma [wp_progress_gen]. In doing so, we can obtain *)
(*     the progress part of the adequacy theorem. *)
(*   *)
  iPureIntro. intros e2 -> Hel.
  eapply (wp_progress_gen hlc);
    [ done | clear stateI Φ fork_post state_interp_mono Hlen1 Hlen3 | done|done].
  iIntros (?).
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iModIntro. iExists _, _, _, _. iFrame.
Qed.

(** Adequacy when using later credits (the default) *)
Definition wp_strong_adequacy := wp_strong_adequacy_gen HasLc.
Global Arguments wp_strong_adequacy _ _ {_}.

(** Since the full adequacy statement is quite a mouthful, we prove some more *)
(* intuitive and simpler corollaries. These lemmas are morover stated in terms of *)
(* [rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

(** This simpler form of adequacy requires the [irisGS] instance that you use *)
(* everywhere to syntactically be of the form *)
(* {| *)
(*   iris_invGS := ...; *)
(*   state_interp σ _ κs _ := ...; *)
(*   fork_post v := ...; *)
(*   num_laters_per_step _ := 0; *)
(*   state_interp_mono _ _ _ _ := fupd_intro _ _; *)
(* |} *)
(* In other words, the state interpretation must ignore [ns] and [nt], the number *)
(* of laters per step must be 0, and the proof of [state_interp_mono] must have *)
(* this specific proof term. *)
(* *)
(** Again, we first prove a lemma generic over the usage of credits. *)
Lemma wp_adequacy_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} s e σ φ :
  (∀ `{Hinv : !invGS_gen hlc Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS_gen hlc Λ Σ :=
           IrisG Hinv (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0)
                 (λ _ _ _ _, fupd_intro _ _)
       in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy_gen hlc Σ _); [ | done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists (λ σ _ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

(** Instance for using credits *)
Definition wp_adequacy := wp_adequacy_gen HasLc.
Global Arguments wp_adequacy _ _ {_}.

Lemma wp_invariance_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invGS_gen hlc Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS_gen hlc Λ Σ := IrisG Hinv (λ σ _, stateI σ) fork_post
              (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
       stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy_gen hlc Σ); [done| |done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists (λ σ _, stateI σ), [(λ _, True)%I], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.

Definition wp_invariance := wp_invariance_gen HasLc.
Global Arguments wp_invariance _ _ {_}.
*)
