(** Adapted from the Coq development of "Mechanized Relational
    Verification of Concurrent Programs with Continuations" ICFP '19

    Original author: Amin Timany *)

From nextgen.case_study.program_logic Require Export weakestpre.
From nextgen.case_study.program_logic Require Import CC_ectx_language CC_ectxi_language CC_ectx_lifting.
From nextgen Require Import nextgen_independent.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Section clwp_def.
  Context {expr val ectx state observation} {Λ : CCEctxLanguage expr val ectx state observation}.
  Context `{irisGS_gen hlc (CC_ectx_lang expr) Σ Ω T}.

Definition clwp_def (c : C) (E : coPset) (e : expr) (Φ : val → iProp Σ) : iProp Σ :=
  (∀ K Ψ, (⚡◻{ Ω ↑ c } ∀ v, Φ v -∗ WP fill K (of_val v) @ ↑c; E {{Ψ}})
            -∗ WP fill K e @ ↑c; E {{Ψ}})%I.
Definition clwp_aux : seal (@clwp_def). by eexists. Qed.
Definition clwp := unseal clwp_aux.
Definition clwp_eq : @clwp = @clwp_def := seal_eq clwp_aux.

End clwp_def.

Instance: Params (@clwp) 8.
Defined.

Notation "'CLWP' e @ ↑ c ; E {{ Φ } }" := (clwp c E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'CLWP'  e  @  ↑ c ; E  {{  Φ  } }") : bi_scope.
Notation "'CLWP' e @ ↑ c {{ Φ } }" := (clwp c ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'CLWP'  e  @  ↑ c  {{  Φ  } }") : bi_scope.

Notation "'CLWP' e @ ↑ c ; E {{ v , Q } }" := (clwp c E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'CLWP'  e  @  ↑ c ; E  {{  v ,  Q  } }") : bi_scope.
Notation "'CLWP' e @ ↑ c {{ v , Q } }" := (clwp c ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'CLWP'  e  @  ↑ c  {{  v ,  Q  } }") : bi_scope.

Section clwp.
  Context {expr val ectx state observation} {Λ : CCEctxLanguage expr val ectx state observation}.
  Context `{irisGS_gen hlc (CC_ectx_lang expr) Σ Ω T}.

  Implicit Types P : iProp Σ.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  
  Lemma clwp_cl {c E e Φ} K :
    CLWP e @ ↑c; E {{Φ}} -∗
    (∀ Ψ, (⚡◻{ Ω ↑ c } ∀ v, Φ v -∗ WP fill K (of_val v) @ ↑c; E {{Ψ}})
            -∗ WP fill K e @ ↑c; E {{Ψ}})%I.
  Proof. rewrite clwp_eq /clwp_def. iIntros "H". iIntros (?). iApply "H". Qed.

  (* Weakest pre *)
  Lemma unfold_clwp (c : C) (E : coPset) (e : expr) (Φ : val → iProp Σ) :
    CLWP e @ ↑c; E {{Φ}} ⊣⊢
         (∀ K Ψ, (⚡◻{ Ω ↑ c } ∀ v, Φ v -∗ WP fill K (of_val v) @ ↑c; E {{Ψ}})
                   -∗ WP fill K e @ ↑c; E {{Ψ}})%I.
  Proof. by rewrite clwp_eq /clwp_def. Qed.

  Lemma clwp_wp (c : C) (E : coPset) (e : expr) (Φ : val → iProp Σ) :
    CLWP e @ ↑c; E {{Φ}} ⊢ WP e @ ↑c; E {{Φ}}.
  Proof.
    iIntros "H". rewrite unfold_clwp.
    iSpecialize ("H" $! empty_ectx Φ with "[]").
    - iApply bnextgen_ind_from_plainly. iModIntro.
      iIntros (w) "Hw". rewrite -> CC_fill_empty.
      iApply wp_value; rewrite /IntoVal /=; eauto using to_of_val.
    - by rewrite CC_fill_empty.
  Qed.

  Global Instance clwp_ne c E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@clwp _ _ _ _ _ Λ _ Σ _ _ _ c E e).
  Proof.
    repeat intros?; rewrite !unfold_clwp.
    repeat (repeat apply forall_ne=>?; repeat apply bnextgen_ind_ne; repeat apply wand_ne; trivial).
  Qed.
  Global Instance clwp_proper c E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@clwp _ _ _ _ _ Λ _ Σ _ _ _ c E e).
  Proof.
      by intros Φ Φ' ?; apply equiv_dist=>n; apply clwp_ne=>v; apply equiv_dist.
  Qed.

  Lemma clwp_value' c E Φ v : Φ v ⊢ CLWP of_val v @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "HΦ"; rewrite unfold_clwp.
    iIntros (K Ψ) "HK". rewrite bnextgen_bounded_ind_elim. iApply ("HK" with "HΦ").
  Qed.
  Lemma clwp_value_inv c E Φ v : CLWP of_val v @ ↑c; E {{ Φ }} ={E}=∗ Φ v.
  Proof. iIntros "H"; iApply wp_value_fupd'. by iApply clwp_wp. Qed.

  Lemma fupd_clwp c E e Φ : (|={E}=> CLWP e @ ↑c; E {{ Φ }}) ⊢ CLWP e @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp.
    iIntros (K Ψ) "HK". iMod "H"; by iApply "H".
  Qed.
  Lemma clwp_fupd c E e Φ : CLWP e @ ↑c; E {{ v, |={E}=> Φ v }} ⊢ CLWP e @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp.
    iIntros (K Ψ) "HK".
    iApply "H". iApply (bnextgen_ind_mono with "HK");iIntros "HK". iIntros (w) ">Hw"; by iApply "HK".
  Qed.

  Lemma clwp_bind c K E e Φ :
    CLWP e @ ↑c; E {{ v, CLWP fill K (of_val v) @ ↑c; E {{ Φ }} }}
    ⊢ CLWP fill K e @ ↑c; E {{ Φ }}.
  Proof.
    iIntros "H"; rewrite !unfold_clwp. iIntros (K' Ψ) "HK'".
    rewrite CC_fill_comp.
    iApply "H".
    rewrite bnextgen_bounded_ind_idemp.
    iApply (bnextgen_ind_mono with "HK'");iIntros "HK'".
    iIntros (v) "Hv".
    rewrite !unfold_clwp -CC_fill_comp.
    iApply "Hv".
    iApply (bnextgen_ind_mono with "HK'");iIntros "HK'".
    iIntros (w) "Hw".
    by iApply "HK'".
  Qed.

  (** * Derived rules *)
  Lemma clwp_mono c E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) →
    CLWP e @ ↑c; E {{ Φ }} ⊢ CLWP e @ ↑c; E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; rewrite !unfold_clwp. iIntros (K χ) "HK".
    iApply "H".
    iApply (bnextgen_ind_mono with "HK");iIntros "HK".
    iIntros (w) "Hw". iApply "HK"; by iApply HΦ.
  Qed.
  Global Instance clwp_mono' c E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@clwp _ _ _ _ _ Λ _ Σ _ _ _ c E e).
  Proof. by intros Φ Φ' ?; apply clwp_mono. Qed.

  Lemma clwp_value c E Φ e v `{!IntoVal e v} : Φ v ⊢ CLWP e @ ↑c; E {{ Φ }}.
  Proof. intros; rewrite -(of_to_val e v) //. by apply clwp_value'. rewrite /IntoVal /= in IntoVal0.
         rewrite -to_of_val IntoVal0 //. Qed.
  Lemma clwp_value_fupd' c E Φ v : (|={E}=> Φ v) ⊢ CLWP of_val v @ ↑c; E {{ Φ }}.
  Proof. intros. by rewrite -clwp_fupd -clwp_value'. Qed.
  Lemma clwp_value_fupd c E Φ e v `{!IntoVal e v} :
    (|={E}=> Φ v) ⊢ CLWP e @ ↑c; E {{ Φ }}.
  Proof. intros. rewrite -clwp_fupd -clwp_value //. Qed.

  Lemma clwp_frame_l c E e Φ R :
    (⚡◻{ Ω ↑ c } R) ∗ CLWP e @ ↑c; E {{ Φ }} ⊢ CLWP e @ ↑c; E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "[HR H]"; rewrite !unfold_clwp. iIntros (K Ψ) "HK".
    iApply "H".
    iDestruct (bnextgen_ind_sep with "[$HR $HK]") as "HR".
    iApply (bnextgen_ind_mono with "HR");iIntros "[HR HK]".
    iIntros (v) "Hv". iApply "HK"; iFrame.
  Qed.
  Lemma clwp_frame_r c E e Φ R :
    CLWP e @ ↑c; E {{ Φ }} ∗ (⚡◻{ Ω ↑ c } R) ⊢ CLWP e @ ↑c; E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "[H HR]"; rewrite !unfold_clwp. iIntros (K Ψ) "HK".
    iApply "H".
    iDestruct (bnextgen_ind_sep with "[$HR $HK]") as "HR".
    iApply (bnextgen_ind_mono with "HR");iIntros "[HR HK]".
    iIntros (v) "Hv". iApply "HK"; iFrame.
  Qed.

  Lemma clwp_wand c E e Φ Ψ :
    CLWP e @ ↑c; E {{ Φ }} -∗ (⚡◻{ Ω ↑ c } (∀ v, Φ v -∗ Ψ v)) -∗ CLWP e @ ↑c; E {{ Ψ }}.
  Proof.
    iIntros "Hwp H". rewrite !unfold_clwp.
    iIntros (K χ) "HK".
    iApply "Hwp".
    iDestruct (bnextgen_ind_sep with "[$H $HK]") as "H".
    iApply (bnextgen_ind_mono with "H");iIntros "[H HK]".    
    iIntros (?) "?"; iApply "HK"; by iApply "H".
  Qed.
  Lemma clwp_wand_l c E e Φ Ψ :
    (⚡◻{ Ω ↑ c } ∀ v, Φ v -∗ Ψ v) ∗ CLWP e @ ↑c; E {{ Φ }} ⊢ CLWP e @ ↑c; E {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (clwp_wand with "Hwp H"). Qed.
  Lemma clwp_wand_r c E e Φ Ψ :
    CLWP e @ ↑c; E {{ Φ }} ∗ (⚡◻{ Ω ↑ c } ∀ v, Φ v -∗ Ψ v) ⊢ CLWP e @ ↑c; E {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (clwp_wand with "Hwp H"). Qed.
End clwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {expr val ectx state observation} {Λ : CCEctxLanguage expr val ectx state observation}.
  Context `{irisGS_gen hlc (CC_ectx_lang expr) Σ Ω T}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Global Instance frame_clwp' p c E e R Φ Ψ `{ind: !GenIndependent2Ω Ω c R} :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p (R) (CLWP e @ ↑c; E {{ Φ }}) (CLWP e @ ↑c; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite ind. rewrite bnextgen_bounded_ind_if_always. rewrite clwp_frame_l. apply clwp_mono, HR. Qed.
  
  Global Instance frame_clwp p c E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p (⚡◻{ Ω ↑ c } R) (CLWP e @ ↑c; E {{ Φ }}) (CLWP e @ ↑c; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite bnextgen_bounded_ind_if_always. rewrite clwp_frame_l. apply clwp_mono, HR. Qed.

  Global Instance is_except_0_clwp c E e Φ : IsExcept0 (CLWP e @ ↑c; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_clwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_clwp p c E e P Φ :
    ElimModal True p false (|==> P) P (CLWP e @ ↑c; E {{ Φ }}) (CLWP e @ ↑c; E {{ Φ }}).
  Proof.
      by rewrite /ElimModal intuitionistically_if_elim
                 (bupd_fupd E) fupd_frame_r wand_elim_r fupd_clwp.
  Qed.

  Global Instance elim_modal_fupd_clwp p c E e P Φ :
    ElimModal True p false (|={E}=> P) P (CLWP e @ ↑c; E {{ Φ }}) (CLWP e @ ↑c; E {{ Φ }}).
  Proof.
      by rewrite /ElimModal intuitionistically_if_elim
                 fupd_frame_r wand_elim_r fupd_clwp.
  Qed.

End proofmode_classes.

(* Section clwp_atomic. *)
(*   Context {expr val ectx state observation} {Λ : CCEctxiLanguage expr val ectx state observation}. *)
(*   Context `{irisGS_gen hlc (CC_ectx_lang expr) Σ} {Hinh : Inhabited state}. *)
(*   Implicit Types P : iProp Σ. *)
(*   Implicit Types Φ : val → iProp Σ. *)
(*   Implicit Types v : val. *)
(*   Implicit Types e : expr. *)
(*   Implicit Types a : A. *)

(*   Lemma clwp_atomic E1 E2 e a Φ : *)
(*     Atomic StronglyAtomic e → sub_values e → is_normal e → *)
(*     (|={E1,E2}=> *)
(*      WP e @ (NotStuck,a); E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ CLWP e @ a; E1 {{ Φ }}. *)
(*   Proof. *)
(*     iIntros (Hatomic Hsv Hin) "H". rewrite !unfold_clwp; simpl in *. *)
(*     iIntros (K' Ψ) "HK". *)
(*     iApply wp_atomic_under_ectx; auto. *)
(*     iMod "H". iModIntro. *)
(*     iApply wp_wand_l; iSplitR "H"; last eauto. *)
(*     iIntros (v) ">Hv". iModIntro. *)
(*     by iApply "HK". *)
(*   Qed. *)

(* End clwp_atomic. *)

(* (** Proofmode class instances *) *)
(* Section proofmode_classes_atomic. *)
(*   Context {expr val ectx state observation} {Λ : CCEctxiLanguage expr val ectx state observation}. *)
(*   Context `{irisGS (CC_ectx_lang expr) Σ} {Hinh : Inhabited state}. *)
(*   Implicit Types P : iProp Σ. *)
(*   Implicit Types Φ : val → iProp Σ. *)
(*   Implicit Types v : val. *)
(*   Implicit Types e : expr. *)


(*   (* lower precedence, if possible, it should always pick elim_upd_fupd_wp *) *)
(*   Global Instance elim_modal_fupd_clwp_atomic p E1 E2 e a P Φ : *)
(*     Atomic StronglyAtomic e → sub_values e → is_normal e → *)
(*     ElimModal True p false (|={E1,E2}=> P) P *)
(*       (CLWP e @ a; E1 {{ Φ }}) (WP e @ (NotStuck,a);E2 {{ v, |={E2,E1}=> Φ v }})%I | 100. *)
(*   Proof. *)
(*     intros. *)
(*     rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r *)
(*             clwp_atomic; auto. *)
(*   Qed. *)

(* End proofmode_classes_atomic. *)
