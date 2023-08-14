From nextgen Require Import nextgen_basic.

Import uPred.

Section bnextgen_rules.
  Context {M : ucmra}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Implicit Types (P Q : uPred M).

  Local Arguments uPred_holds {_} !_ _ _ /.

  Lemma nextgen_id P : (⚡={id}=> P) ⊣⊢ P.
  Proof.
    apply bnextgen_id.    
    auto.
  Qed.

End bnextgen_rules.
