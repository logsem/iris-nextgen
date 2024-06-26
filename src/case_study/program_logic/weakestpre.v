From iris.proofmode Require Import base proofmode classes.
(* From iris.base_logic.lib Require Export fancy_updates. *)
From iris.program_logic Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
(* From iris.bi Require Export weakestpre. *)
From nextgen Require Export bi_weakestpre.
From iris.prelude Require Import options.
From nextgen.lib Require Export fancy_updates.
Import uPred.
From nextgen Require Export utils nextgen_soundness nextgen_persistently
  nextgen_basic nextgen_pointwise nextgen_independent.

Class irisGS_gen (hlc : has_lc) (Λ : language) (Σ : gFunctors) (Ω : gTransformations Σ) (A : cmra) := IrisG {
  iris_pick :> pick_transform_rel A;
  iris_invGS :> invGIndS_gen hlc Σ Ω A iris_pick;
                                                                                               
  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list (observation Λ)] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state Λ → nat → list (observation Λ) → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;

  (** A method that chooses whether to instantiate a generation change
  indexed by C, based on the current expression *)
  next_choose : expr Λ -> option C;
                                                                      

  (** The number of additional logical steps (i.e., later modality in the
  definition of WP) and later credits per physical step is
  [S (num_laters_per_step ns)], where [ns] is the number of physical steps
  executed so far. We add one to [num_laters_per_step] to ensure that there
  is always at least one later and later credit for each physical step. *)
  num_laters_per_step : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns κs nt :
    (state_interp σ ns κs nt) ⊢ state_interp σ (S ns) κs nt
}.
Global Opaque iris_invGS.
Global Arguments IrisG {hlc Λ Σ}.

Notation irisGS := (irisGS_gen HasNoLc).

Local Lemma transform_mono {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ) :
  (⚡={Ω}=> P) ⊢ ⚡={Ω}=> P.
Proof.
  apply nextgen_basic.bnextgen_mono.
  iIntros "HP";done.
Qed.

Local Lemma transform_later {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ) :
  (▷ ⚡={Ω}=> P) ⊢ ⚡={Ω}=> ▷ P.
Proof.
  rewrite nextgen_basic.bnextgen_later.
  auto.
Qed.

Local Lemma transform_plain {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ) :
  (■ P) ⊢ ⚡={Ω}=> ■ P.
Proof.
  iIntros "#HP".
  iApply nextgen_basic.bnextgen_intro_plainly. eauto.
Qed.

#[local] Instance insert_mono_into_pnextgen {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ)
  : IntoPnextgen Ω _ _ := transform_mono P.
#[local] Instance insert_later_into_pnextgen {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ)
  : IntoPnextgen Ω _ _ := transform_later P.
#[local] Instance insert_plain_into_pnextgen {Σ : gFunctors} {Ω : gTransformations Σ} (P : iProp Σ)
  : IntoPnextgen Ω _ _ := transform_plain P.

Class SameGeneration `{irisgen : irisGS_gen hlc Λ Σ Ω A} (e : expr Λ) : Prop :=
  same_generation : next_choose e = None.

Notation "?={ Ω <- e }=> P" := (@bnextgen_option _ Ω _ _ _ _ _ next_choose e P)
                               (at level 99, Ω at level 50, e at level 50, P at level 200, format "?={ Ω  <-  e }=>  P") : bi_scope.

(* Notation "⚡◻{ Ω <- c } P" := (⚡◻{ transmap_insert_two_inG (inv_pick_transform c) (C_pick c) Ω } P)%I *)
(*                            (at level 99, Ω at level 50, c at level 20, P at level 200, format "⚡◻{ Ω  <-  c }  P") : bi_scope. *)


Definition bounded_nextgen `{!irisGS_gen hlc Λ Σ Ω A} (c : C) (e : expr Λ) :=
  from_option (λ c', rc CR c c') True (next_choose e).
  
(** The predicate we take the fixpoint of in order to define the WP. *)
(** In the step case, we both provide [S (num_laters_per_step ns)]
  later credits, as well as an iterated update modality that allows
  stripping as many laters, where [ns] is the number of steps already taken.
  We have both as each of these provides distinct advantages:
  - Later credits do not have to be used right away, but can be kept to
    eliminate laters at a later point.
  - The step-taking update composes well in parallel: we can independently
    compose two clients who want to eliminate their laters for the same
    physical step, which is not possible with later credits, as they
    can only be used by exactly one client.
  - The step-taking update can even be used by clients that opt out of
    later credits, e.g. because they use [BiFUpdPlainly]. *)
Definition wp_pre `{!irisGS_gen hlc Λ Σ Ω A} (s : stuckness)
    (wp : C -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  C -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ l_bound E e1 Φ,
  (match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
         £ (S (num_laters_per_step ns))
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
         ⌜bounded_nextgen l_bound e1⌝ ∗
         (?={Ω <- e1}=> state_interp σ2 (S ns) κs (length efs + nt)) ∗
         (?={Ω <- e1}=> wp l_bound E e2 Φ) ∗
         [∗ list] i ↦ ef ∈ efs, wp C_bot ⊤ ef fork_post
  end)%I.

Local Instance wp_pre_contractive `{!irisGS_gen hlc Λ Σ Ω A} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp l_bound E e1 Φ.
  do 25 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IH]; simpl.
  - unfold bnextgen_option. case_match; repeat (apply nextgen_basic.bnextgen_ne || f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

Local Definition wp_def `{!irisGS_gen hlc Λ Σ Ω A} : Wp (iProp Σ) (expr Λ) (val Λ) (stuckness * C) := λ sc, fixpoint (wp_pre sc.1) sc.2.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {hlc Λ Σ Ω A _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!irisGS_gen hlc Λ Σ Ω A} : wp = @wp_def hlc Λ Σ Ω A _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS_gen hlc Λ Σ Ω A}.
Implicit Types s : stuckness.
Implicit Types c : C.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s c E e Φ :
  WP e @ s; ↑c; E {{ Φ }} ⊣⊢ wp_pre s (λ c, wp (PROP:=iProp Σ) (s,c)) c E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne c s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) (s,c) E e).
Proof.
  revert e s. induction (lt_wf n) as [n _ IH]=> e s Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 25 (apply nextgen_basic.bnextgen_ne || f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  unfold bnextgen_option. case_match;
    [do 5 ((apply nextgen_basic.bnextgen_ne) || f_contractive || f_equiv)
    | do 3 (f_contractive || f_equiv)].
  all: rewrite IH; [done|lia|]; intros v'; eapply dist_le; [apply HΦ|lia].
Qed.
Global Instance wp_proper s c E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) (s,c) E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive s c E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) (s,c) E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 24 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  do 4 f_equiv. unfold bnextgen_option.
  case_match;[apply bnextgen_ne|]; do 2 f_equiv;auto.
Qed.

Lemma wp_value_fupd' s c E Φ v : WP of_val v @ s; ↑c; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

Global Instance stuckness_C_le : SqSubsetEq C := λ c1 c2, rc CR c1 c2.

Global Instance stuckness_C_le_transitive : Transitive stuckness_C_le.
Proof.
  intros ??? Hcr1 Hcr2.
  simpl in *.
  inversion Hcr1;inversion Hcr2;subst;auto.
  constructor. etrans;eauto.
Qed.
Global Instance stuckness_C_le_reflexive : Reflexive stuckness_C_le.
Proof.
  intros ?.
  apply rc_l.
Qed.
  
Lemma wp_strong_mono s1 s2 c1 c2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → c2 ⊑ c1 -> E1 ⊆ E2 →
  WP e @ s1; ↑c1; E1 {{ Φ }} -∗ (⚡◻{ Ω ↑ c1 } (∀ v, (Φ v ={E2}=∗ Ψ v))) -∗ WP e @ s2; ↑c2; E2 {{ Ψ }}.
Proof.
  simpl. intros Hle. revert e c1 c2 E1 E2 Φ Ψ.
  iApply löb_wand_plainly. iModIntro.
  iIntros "#IH". iIntros (e c1 c2 E1 E2 Φ Ψ HC HE) "H HΦ".
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { (* destruct a_inhabited as [a]. *)
    iDestruct (bnextgen_bounded_ind_elim with "HΦ") as "HΦ".
    iApply ("HΦ" with "[> -]"). iApply (fupd_mask_mono E1 _);auto. }
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("H" with "[//] Hcred") as "H". iIntros "!> !>".  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros ">(%Hbounded & $ & H & Hefs)". iMod "Hclose" as "_". iModIntro.
  iSplitR.
  { iPureIntro. rewrite /bounded_nextgen in Hbounded.
    rewrite /bounded_nextgen. destruct (next_choose e);auto;simpl in *.
    inversion HC;subst;auto.
    etrans;eauto. }
  iSplitR "Hefs".
  - unfold bnextgen_option. rewrite /bounded_nextgen in Hbounded. destruct (next_choose e).
    + simpl in Hbounded. iDestruct (bnextgen_bounded_ind_bnextgen_intro with "HΦ") as "HΦ";[eauto|].
      iModIntro.
      iApply ("IH" $! e2 with "[] [//] H"); auto.
    + iApply ("IH" $! e2 with "[//] [//] H"); auto.
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] [] H"); auto.
    iApply bnextgen_bounded_ind_GenIndependent_intro;[|auto].
    iIntros (??) "_". iModIntro. auto.
Qed.

(* A weaker variant with a Plainly consequence *)
Lemma wp_strong_mono_plainly s1 s2 c1 c2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → c2 ⊑ c1 -> E1 ⊆ E2 →
  WP e @ s1; ↑c1; E1 {{ Φ }} -∗ (■ (∀ v, (Φ v ={E2}=∗ Ψ v))) -∗ WP e @ s2; ↑c2; E2 {{ Ψ }}.
Proof.
  iIntros (Hs Hc HE)  "Hwp Hcon".
  iDestruct (bnextgen_ind_from_plainly with "Hcon") as "Hcon".
  iApply (wp_strong_mono with "[$] [$]");eauto.
Qed.

Lemma fupd_wp s c E e Φ : (|={E}=> WP e @ s; ↑c; E {{ Φ }}) ⊢ WP e @ s; ↑c; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s c E e Φ : WP e @ s; ↑c; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; ↑c; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono_plainly s s c c E with "H"); auto. Qed.

Lemma wp_atomic s c E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} `{!SameGeneration e} :
  (|={E1,E2}=> WP e @ s; ↑c; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; ↑c; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns κ κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (e2 σ2 efs Hstep) "Hcred".
  iApply (step_fupdN_wand with "(H [//] Hcred)").
  iIntros ">(%Hbounded & Hσ & H & Hefs)". destruct s.
  - rewrite /bnextgen_option SameGeneration0.
    rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ _ [] with "[$]") as "[H _]".
      iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - rewrite /bnextgen_option SameGeneration0.
    destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite wp_value_fupd'. iMod "H" as ">H".
    iModIntro. iFrame "Hσ Hefs". iFrame "%". by iApply wp_value_fupd'.
Qed.

(** This lemma gives us access to the later credits that are generated in each step,
  assuming that we have instantiated [num_laters_per_step] with a non-trivial (e.g. linear)
  function.
  This lemma can be used to provide a "regeneration" mechanism for later credits.
  [state_interp] will have to be defined in a way that involves the required regneration
  tokens. TODO: point to an example of how this is used.

  In detail, a client can use this lemma as follows:
  * the client obtains the state interpretation [state_interp _ ns _ _],
  * it uses some ghost state wired up to the interpretation to know that
    [ns = k + m], and update the state interpretation to [state_interp _ m _ _],
  * _after_ [e] has finally stepped, we get [num_laters_per_step k] later credits
    that we can use to prove [P] in the postcondition, and we have to update
    the state interpretation from [state_interp _ (S m) _ _] to
    [state_interp _ (S ns) _ _] again. *)
Lemma wp_credit_access s c E e Φ P :
  TCEq (to_val e) None →
  (∀ m k, num_laters_per_step m + num_laters_per_step k ≤ num_laters_per_step (m + k)) →
  (∀ σ1 ns κs nt, (state_interp σ1 ns κs nt) ={E}=∗
    ∃ k m, (state_interp σ1 m κs nt) ∗ ⌜ns = (m + k)%nat⌝ ∗
    (∀ nt σ2 κs, £ (num_laters_per_step k) -∗ (?={Ω <- e}=> state_interp σ2 (S m) κs nt) ={E}=∗
      (?={Ω <- e}=> state_interp σ2 (S ns) κs nt) ∗ ⚡◻{Ω ↑ c} P)) -∗
  WP e @ s; ↑c; E {{ v, P ={E}=∗ Φ v }} -∗
  WP e @ s; ↑c; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> Htri) "Hupd Hwp".
  iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("Hupd" with "Hσ1") as (k m) "(Hσ1 & -> & Hpost)".
  iMod ("Hwp" with "Hσ1") as "[$ Hwp]". iModIntro.
  iIntros (e2 σ2 efs Hstep) "Hc".
  iDestruct "Hc" as "[Hone Hc]".
  iPoseProof (lc_weaken with "Hc") as "Hc"; first apply Htri.
  iDestruct "Hc" as "[Hm Hk]".
  iCombine "Hone Hm" as "Hm".
  iApply (step_fupd_wand with "(Hwp [//] Hm)"). iIntros "Hwp".
  iApply (step_fupdN_le (num_laters_per_step m)); [ | done | ].
  { etrans; last apply Htri. lia. }
  iApply (step_fupdN_wand with "Hwp"). iIntros ">(%Hbounded & SI & Hwp & $)".
  iMod ("Hpost" with "Hk SI") as "[$ HP]". iModIntro.
  iFrame "%".
  rewrite /bounded_nextgen in Hbounded.
  unfold bnextgen_option;case_match.
  1: iDestruct (bnextgen_bounded_ind_bnextgen_intro with "HP") as "HP";[eauto|].
  1: iModIntro.
  all: iApply (wp_strong_mono with "Hwp"); [by auto..|].
  all: iApply (bnextgen_ind_mono with "HP");iIntros "HP".
  all: iIntros (v) "HΦ"; iApply ("HΦ" with "HP").
Qed.

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
Lemma wp_step_fupdN_strong n s c E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, (state_interp σ ns κs nt)
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
   ((⚡◻{Ω ↑ c} (|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> ⚡◻{Ω ↑ c} P)) ∗
    WP e @ s; ↑c; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; ↑c; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iApply (bnextgen_ind_mono with "HP");iIntros "HP".
    iIntros (v) "H". iApply ("H" with "[>HP]").
    rewrite fupd_trans. iMod "HP". iModIntro.
    iApply bnextgen_ind_elim. eauto. }
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H".
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [HP Hwp]]".
  iDestruct (bnextgen_ind_elim with "HP") as "HP".
  iMod "HP".
  iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP".
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred". iMod ("H" $! e2 σ2 efs with "[% //] Hcred") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupdN_wand with "H"). iIntros ">(%Hb & $ & Hwp & $)". iMod "HP".
    iModIntro. iFrame "%".
    rewrite /bounded_nextgen in Hb.
    unfold bnextgen_option;case_match.
    1: iDestruct (bnextgen_bounded_ind_bnextgen_intro with "HP") as "HP";[eauto|].
    1: iModIntro.
    all: iApply (wp_strong_mono with "Hwp");auto.
    all: iApply (bnextgen_ind_mono with "HP");iIntros "HP".
    all: iIntros (v) "HΦ".
    all: iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma wp_bind K `{!LanguageCtx K} s c E e Φ :
  (forall e, to_val e = None -> next_choose (K e) = next_choose e) ->
  WP e @ s; ↑c; E {{ v, WP K (of_val v) @ s; ↑c; E {{ Φ }} }} ⊢ WP K e @ s; ↑c; E {{ Φ }}.
Proof.
  intros next_state_ctx.
  iRevert (E e Φ).
  iApply löb_wand_plainly. iModIntro.
  iIntros "#IH" (E e Φ) "H".
  rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 step κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]".
  simpl in *.
  iModIntro; iSplit.
  { destruct s;eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep) "Hcred".
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//] Hcred") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "(%Hb & HH & H & Htp)". iModIntro.
  rewrite /bounded_nextgen in Hb.
  unfold bnextgen_option. rewrite next_state_ctx//.
  iFrame. rewrite /bounded_nextgen. rewrite next_state_ctx//.
  destruct (next_choose e);iFrame "%";[iModIntro|];by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s c E e Φ :
  (forall e, to_val e = None -> next_choose (K e) = next_choose e) ->
  WP K e @ s; ↑c; E {{ Φ }} ⊢ WP e @ s; ↑c; E {{ v, WP K (of_val v) @ s; ↑c; E {{ Φ }} }}.
Proof.
  intros next_state_ctx. iRevert (E e Φ).
  iApply löb_wand_plainly. iModIntro.
  iIntros "#IH" (E e Φ) "H".
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite language.fill_not_val //.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]".
  simpl in *.
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("H" $! _ _ _ with "[] Hcred") as "H"; first eauto using fill_step.
  iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H" as "(%Hb & HH & H & Htp)". iModIntro.
  rewrite /bounded_nextgen in Hb.
  unfold bnextgen_option. rewrite next_state_ctx//.
  iFrame. rewrite /bounded_nextgen. rewrite next_state_ctx// in Hb.
  destruct (next_choose e);iFrame "%";[iModIntro|]; by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s c E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; ↑c; E {{ Φ }} ⊢ WP e @ s; ↑c; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono_plainly with "H"); auto. iModIntro.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 c E e Φ :
  s1 ⊑ s2 → WP e @ s1; ↑c; E {{ Φ }} ⊢ WP e @ s2; ↑c; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono_plainly with "H"); auto. Qed.
Lemma wp_bound_mono s c1 c2 E e Φ :
  c2 ⊑ c1 → WP e @ s; ↑c1; E {{ Φ }} ⊢ WP e @ s; ↑c2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono_plainly with "H"); auto. Qed.
Lemma wp_stuck_weaken s c E e Φ :
  WP e @ s; ↑c; E {{ Φ }} ⊢ WP e @ ↑c; E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s c E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; ↑c; E1 {{ Φ }} ⊢ WP e @ s; ↑c; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono_plainly with "H"); auto. Qed.
Global Instance wp_mono' s c E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) (s,c) E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s c E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) (s,c) E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s c E Φ e v : IntoVal e v → WP e @ s; ↑c; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s c E Φ v : Φ v ⊢ WP (of_val v) @ s; ↑c; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s c E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; ↑c; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s c E e Φ R : (⚡◻{Ω ↑ c} R) ∗ WP e @ s; ↑c; E {{ Φ }} ⊢ WP e @ s; ↑c; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[R H]".
  iApply (wp_strong_mono with "H");auto.
  iApply (bnextgen_ind_mono with "R");iIntros "HR".
  auto with iFrame.
Qed.
Lemma wp_frame_r s c E e Φ R : WP e @ s; ↑c; E {{ Φ }} ∗ (⚡◻{Ω ↑ c} R) ⊢ WP e @ s; ↑c; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros "[H R]".
  iApply (wp_strong_mono with "H"); auto.
  iApply (bnextgen_ind_mono with "R");iIntros "HR".
  auto with iFrame.
Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the WP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma wp_step_fupdN n s c E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, (state_interp σ ns κs nt)
       ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
  ((⚡◻{Ω ↑ c} (|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> ⚡◻{Ω ↑ c} P)) ∗
    WP e @ s; ↑c; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; ↑c; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
  iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
  iApply (bnextgen_ind_mono with "HP");iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.
Lemma wp_step_fupd s c E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (⚡◻{Ω ↑ c} |={E1}[E2]▷=> ⚡◻{Ω ↑ c} P) -∗ WP e @ s; ↑c; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; ↑c; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong 1 _ _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iApply (bnextgen_ind_mono with "HR");iIntros "HR".
    iMod "HR" as "$". auto.
Qed.

Lemma wp_frame_step_l s c E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (⚡◻{Ω ↑ c} |={E1}[E2]▷=> ⚡◻{Ω ↑ c} R) ∗ WP e @ s; ↑c; E2 {{ Φ }} ⊢ WP e @ s; ↑c; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s c E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; ↑c; E2 {{ Φ }} ∗ (⚡◻{Ω ↑ c} |={E1}[E2]▷=> ⚡◻{Ω ↑ c} R) ⊢ WP e @ s; ↑c; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; ↑_; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s c E e Φ R :
  TCEq (to_val e) None → (▷ ⚡◻{Ω ↑ c} R) ∗ WP e @ s; ↑c; E {{ Φ }} ⊢ WP e @ s; ↑c; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "[??]".
  iApply (wp_frame_step_l s c E E); try iFrame; eauto.
  rewrite bnextgen_ind_later.
  rewrite -/(bnextgen_bounded_ind _ _ _).
  rewrite bnextgen_bounded_ind_idemp.
  iApply (bnextgen_ind_mono with "[$]");iIntros "HP".
  iDestruct (bnextgen_ind_later with "HP") as "HP".
  iModIntro. iNext. iModIntro.
  auto.
Qed.
Lemma wp_frame_step_r' s c E e Φ R :
  TCEq (to_val e) None → WP e @ s; ↑c; E {{ Φ }} ∗ (▷ ⚡◻{Ω ↑ c} R) ⊢ WP e @ s; ↑c; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros (?) "[??]".
  iApply (wp_frame_step_r s c E E); try iFrame; eauto.
  rewrite bnextgen_ind_later.
  rewrite -/(bnextgen_bounded_ind _ _ _).
  rewrite bnextgen_bounded_ind_idemp.
  iApply (bnextgen_ind_mono with "[$]");iIntros "HP".
  iDestruct (bnextgen_ind_later with "HP") as "HP".
  iModIntro. iNext. iModIntro.
  auto.
Qed.

Lemma wp_wand s c E e Φ Ψ :
  WP e @ s; ↑c; E {{ Φ }} -∗ (⚡◻{Ω ↑ c} (∀ v, Φ v -∗ Ψ v)) -∗ WP e @ s; ↑c; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iApply (bnextgen_ind_mono with "H");iIntros "H".
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s c E e Φ Ψ :
  (⚡◻{Ω ↑ c} (∀ v, Φ v -∗ Ψ v)) ∗ WP e @ s; ↑c; E {{ Φ }} ⊢ WP e @ s; ↑c; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s c E e Φ Ψ :
  WP e @ s; ↑c; E {{ Φ }} ∗ (⚡◻{Ω ↑ c} (∀ v, Φ v -∗ Ψ v)) ⊢ WP e @ s; ↑c; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s c E e Φ R :
  (⚡◻{Ω ↑ c} R) -∗ WP e @ s; ↑c; E {{ v, R -∗ Φ v }} -∗ WP e @ s; ↑c; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iApply (bnextgen_ind_mono with "HR");iIntros "H".
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS_gen hlc Λ Σ Ω A}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp' p s c E e R Φ Ψ `{ind: !GenIndependent2Ω Ω c R} :
    (∀ v, Frame p (R) (Φ v) (Ψ v)) →
    Frame p (R) (WP e @ s; ↑c; E {{ Φ }}) (WP e @ s; ↑c; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR.
    rewrite ind.
    rewrite bnextgen_bounded_ind_if_always.
    rewrite wp_frame_l. apply wp_mono,HR.
  Qed.

  Global Instance frame_wp p s c E e R Φ Ψ :
    (∀ v, Frame p (R) (Φ v) (Ψ v)) →
    Frame p (⚡◻{Ω ↑ c} R) (WP e @ s; ↑c; E {{ Φ }}) (WP e @ s; ↑c; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR.
    rewrite bnextgen_bounded_ind_if_always.
    rewrite wp_frame_l. apply wp_mono,HR.
  Qed.

  Global Instance is_except_0_wp s c E e Φ : IsExcept0 (WP e @ s; ↑c; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s c E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; ↑c; E {{ Φ }}) (WP e @ s; ↑c; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s c E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; ↑c; E {{ Φ }}) (WP e @ s; ↑c; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s c E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e ∧ SameGeneration e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; ↑c; E1 {{ Φ }}) (WP e @ s; ↑c; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros [??]. rewrite intuitionistically_if_elim fupd_frame_r wand_elim_r.
    iApply wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s c E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; ↑c; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  (* Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ : *)
  (*   ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s.1) e ∧ SameGeneration e) *)
  (*           (fupd E1 E2) (fupd E2 E1) *)
  (*           α β γ (WP e @ s; E1 {{ Φ }}) *)
  (*           (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100. *)
  (* Proof. *)
  (*   iIntros ([??]) "Hinner Hacc". unfold accessor. *)
  (*   iApply (wp_atomic _ _ E2). *)
  (*   iMod "Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply (wp_wand with "(Hinner Hα)"). *)
    
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (*   rewrite -wp_atomic. iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply (wp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)

  (* Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ : *)
  (*   ElimAcc (X:=X) True (fupd E E) (fupd E E) *)
  (*           α β γ (WP e @ s; E {{ Φ }}) *)
  (*           (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply wp_fupd. *)
  (*   iApply (wp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)
  
End proofmode_classes.
