(* This file defines the "next-current" generational camera.

   For a camera [A] the camera [gen_nc A] contains two elements of [A]. The
   first element is called "next" and it is carried through generations and
   will be the current element in the next geneation. The second element is
   called "current" and is owned for the current generation but discarded going
   into the next generation.

   The construction uses a product and an option. The option serves to force the
   core to be a totalt function. Otherwise the generational transformation
   would not commute with the core for an element [(a_p, a_v)] where the core
   is defined for [a_p] but not for [a_v]. *)

From iris.algebra Require Import cmra.

From self Require Import cmra_morphism_extra.

Definition gen_nc (A : cmra) : Type := option A * option A.
Definition gen_ncR (A : cmra) : cmra := prodR (optionR A) (optionR A).
Definition gen_ncUR (A : ucmra) : cmra := prodUR (optionUR A) (optionUR A).

Definition gen_nc_trans {A : cmra} (p : gen_nc A) : gen_nc A :=
  match p with (a_p, a_v) => (a_p, a_p) end.

#[global]
Instance gen_nc_trans_gentrans A : CmraMorphism (gen_nc_trans (A := A)).
Proof.
  split.
  - intros n [??] [??]. simpl.
    intros [eq ?]. simpl in eq. rewrite eq.
    done.
  - intros ? [??] [??]. done.
  - intros [??]. done.
  - intros [??] [??]. done.
Qed.

Section pv.
  Context `{A : cmra}.
  Implicit Type (a : A).

  Inductive pv_stat := sP | sPV | sV.

  Definition mk_gen_nc (p : pv_stat) a :=
    match p with
      | sV => (None, Some a)
      | sP => (Some a, None)
      | sPV => (Some a, Some a)
    end.

  (* [a] is both persisted and volatile. *)
  Definition gNC (a : A) : gen_nc A := mk_gen_nc sPV a.
  (* [a] is volatile. *)
  Definition gC (a : A) : gen_nc A := mk_gen_nc sV a.
  (* [a] is persisted. *)
  Definition gN (a : A) : gen_nc A := mk_gen_nc sP a.

  Lemma gen_nc_trans_p a :
    gen_nc_trans (gN a) = gNC a.
  Proof. done. Qed.

  Lemma gen_nc_valid p a : ✓ (mk_gen_nc p a) ↔ ✓ a.
  Proof.
    destruct p; rewrite pair_valid Some_valid; naive_solver.
  Qed.

  Lemma gen_nc_op p a1 a2 :
    mk_gen_nc p a1 ⋅ mk_gen_nc p a2 ≡ mk_gen_nc p (a1 ⋅ a2).
  Proof. destruct p; done. Qed.

  #[global] Instance mk_gen_nc_proper p a :
  Proper ((≡) ==> (≡)) (mk_gen_nc p).
  Proof. solve_proper. Qed.

  (* As long as one status is [PV] the operation guarantees validity of the
   * composition of two elements. *)
  Lemma gen_nc_op_valid p a1 a2 :
    ✓ ((gNC a1) ⋅ (mk_gen_nc p a2)) ↔ ✓ (a1 ⋅ a2).
  Proof.
    destruct p; rewrite pair_valid Some_valid; split; try naive_solver; simpl.
    - intros V. split; first done. apply cmra_valid_op_l in V. done.
    - intros V. split; last done. eapply cmra_valid_op_l. done.
  Qed.

  Lemma gen_nc_update p a a' :
    a ~~> a' →
    mk_gen_nc p a ~~> mk_gen_nc p a'.
  Proof.
    intros ?. destruct p; apply prod_update; try apply option_update; done.
  Qed.

End pv.
