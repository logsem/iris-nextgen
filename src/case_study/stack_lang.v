Require Export Logic.FunctionalExtensionality.
From iris.program_logic Require Import language.
From self.case_study.program_logic Require Import CC_ectx_lifting CC_ectxi_language. 
From self.case_study Require Import prelude.
From stdpp Require Import binders strings gmap.

Definition loc := positive.

Global Instance loc_dec_eq : EqDecision loc.
Proof. solve_decision. Defined.

Global Instance loc_countable : Countable loc.
Proof. apply pos_countable. Qed.

Inductive binop := Add | Sub | Eq | Le | Lt.

Global Instance binop_dec_eq : EqDecision binop.
Proof. solve_decision. Defined.

Inductive tag :=
| global : tag
| borrow : tag
| local : Z -> tag.

Global Instance tag_dec_eq : EqDecision tag.
Proof. solve_decision. Defined.

Module lang.

  (*** Syntax *)
  
  Inductive expr :=
  (* Variable Bindings *)
  | Var (x : string)
  | Lam (δ : tag) (k x : binder) (e : expr)
  | LetIn (x : binder) (e1 : expr) (e2 : expr)
  (* Base Types *)
  | Nat (n : nat)
  | Bool (b : bool)
  | Unit
  | BinOp (op : binop) (e1 e2 : expr)
  (* Reference Types *)
  | Loc (δ : tag) (l : loc)
  | Halloc (e : expr)
  | Salloc (e : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | Mask (e : expr)
  (* Control Flow *)
  | Cont (i : Z) (K : list ectx_item)
  | Call (e1 : expr) (e2 : expr)
  | Return (e1 : expr) (e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* If then else *)
  | If (e0 e1 e2 : expr)

  with ectx_item :=
  | LetInCtx (x : binder) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | HallocCtx
  | SallocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | MaskCtx
  | CallLCtx (e2 : expr)
  | CallRCtx (v1 : val)
  | ReturnLCtx (e2 : expr)
  | ReturnRCtx (v1 : val)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | IfCtx (e1 e2 : expr)

  with val :=
  | LamV (δ : tag) (k x : binder) (e : expr)
  | NatV (n : nat)
  | BoolV (b : bool)
  | UnitV
  | LocV (δ : tag) (l : loc)
  | ContV (i : Z) (K : list ectx_item)
  | PairV (v1 v2 : val)
  .

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Lam δ k x e => Some (LamV δ k x e)
    | Nat n => Some (NatV n)
    | Bool b => Some (BoolV b)
    | Unit => Some UnitV
    | Loc δ l => Some (LocV δ l)
    | Cont i K => Some (ContV i K)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2) 
| _ => None
  end.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV δ k x e => Lam δ k x e
    | NatV n => Nat n
    | BoolV b => Bool b
    | UnitV => Unit
    | LocV δ l => Loc δ l
    | ContV i K => Cont i K
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    end.

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | CallLCtx e2 => Call e e2
    | CallRCtx v1 => Call (of_val v1) e
    | LetInCtx x e2 => LetIn x e e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | IfCtx e1 e2 => If e e1 e2
    | HallocCtx => Halloc e
    | SallocCtx => Salloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    | MaskCtx => Mask e
    | ReturnLCtx e2 => Return e e2
    | ReturnRCtx v1 => Return (of_val v1) e
    end.

  (* Notation for bool and nat *)
  Notation "#♭ b" := (Bool b) (at level 20).
  Notation "#n n" := (Nat n) (at level 20).
  (* Notation for bool and nat *)
  Notation "'#♭v' b" := (BoolV b) (at level 20).
  Notation "'#nv' n" := (NatV n) (at level 20).
  
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. induction v;eauto. by simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
  Proof. revert v; induction e =>v Hv; simplify_option_eq;auto. f_equiv;auto. Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma of_val_dec_eq v1 v2 :
    Decision (of_val v1 = of_val v2) → Decision (v1 = v2).
  Proof.
    destruct 1 as [Hv%of_val_inj|Hv]; [left| right => Hw; rewrite Hw in Hv]; done.
  Qed.

  Global Instance val_inh : Inhabited val := populate UnitV.

  
  (*** Substitution *)

  (* Definition bind_ren (sb : string -> string) : binder -> binder := *)
  (*   fun b => match b with | BAnon => BAnon | BNamed s => BNamed (sb s) end. *)
  Fixpoint expr_rename (x y : string) (e : expr) : expr :=
    match e with
    | Var z => Var $ if decide (x = z) then y else z
    | Lam δ k z e =>
        if decide (BNamed x = k) then Lam δ (BNamed y) z e
        else if decide (BNamed x = z) then Lam δ k (BNamed y) e
             else Lam δ k z (expr_rename x y e)
    | LetIn z e1 e2 =>
        if decide (BNamed x = z) then LetIn (BNamed y) (expr_rename x y e1) (expr_rename x y e2)
        else LetIn z (expr_rename x y e1) (expr_rename x y e2)
    | Call e1 e2 => Call (expr_rename x y e1) (expr_rename x y e2)
    | Unit => Unit
    | Nat n => Nat n
    | Bool b => Bool b
    | BinOp op e1 e2 => BinOp op (expr_rename x y e1) (expr_rename x y e2)
    | If e0 e1 e2 => If (expr_rename x y e0) (expr_rename x y e1) (expr_rename x y e2)
    | Pair e1 e2 => Pair (expr_rename x y e1) (expr_rename x y e2)
    | Fst e => Fst (expr_rename x y e)
    | Snd e => Snd (expr_rename x y e)
    | Loc δ l => Loc δ l
    | Halloc e => Halloc (expr_rename x y e)
    | Salloc e => Salloc (expr_rename x y e)
    | Mask e => Mask (expr_rename x y e)
    | Load e => Load (expr_rename x y e)
    | Store e1 e2 => Store (expr_rename x y e1) (expr_rename x y e2)
    | Return e1 e2 => Return (expr_rename x y e1) (expr_rename x y e2)
    | Cont i K => Cont i (map (ectx_item_rename x y) K)
    end
  with ectx_item_rename (x y : string) (K : ectx_item) : ectx_item :=
         match K with
         | LetInCtx z e2 =>
             if decide (BNamed x = z) then LetInCtx (BNamed y) (expr_rename x y e2)
             else LetInCtx z (expr_rename x y e2)
         | BinOpRCtx op v1 => BinOpRCtx op (val_rename x y v1)
         | BinOpLCtx op e2 => BinOpLCtx op (expr_rename x y e2)
         | HallocCtx => HallocCtx
         | SallocCtx => SallocCtx
         | LoadCtx => LoadCtx
         | StoreLCtx e2 => StoreLCtx (expr_rename x y e2)
         | StoreRCtx v1 => StoreRCtx (val_rename x y v1)
         | MaskCtx => MaskCtx
         | CallLCtx e2 => CallLCtx (expr_rename x y e2)
         | CallRCtx v1 => CallRCtx (val_rename x y v1)
         | ReturnLCtx e2 => ReturnLCtx (expr_rename x y e2)
         | ReturnRCtx v1 => ReturnRCtx (val_rename x y v1)
         | PairLCtx e2 => PairLCtx (expr_rename x y e2)
         | PairRCtx v1 => PairRCtx (val_rename x y v1)
         | FstCtx => FstCtx
         | SndCtx => SndCtx
         | IfCtx e1 e2 => IfCtx (expr_rename x y e1) (expr_rename x y e2)
         end
  with val_rename (x y : string) (v : val) : val :=
         match v with
         | LamV δ k z e =>
             if decide (BNamed x = k) then LamV δ (BNamed y) z e
             else if decide (BNamed x = z) then LamV δ k (BNamed y) e
                  else LamV δ k z (expr_rename x y e)
         | NatV n => NatV n
         | BoolV b => BoolV b
         | UnitV => UnitV
         | LocV δ l => LocV δ l
         | ContV i K => ContV i (map (ectx_item_rename x y) K)
         | PairV v1 v2 => PairV (val_rename x y v1) (val_rename x y v2)
         end.

  (** Substitution, replaces occurrences of [x] in [e] with [v]. *)
  Fixpoint expr_subst (x : string) (v : val) (e : expr) : expr :=
    match e with
    | Var y => if decide (x = y) then of_val v else Var x
    | Lam δ k y e =>
        Lam δ k y $
          if decide (BNamed x ≠ k ∧ BNamed x ≠ y)
          then expr_subst x v e
          else e
    | LetIn y e1 e2 => 
        if decide (BNamed x ≠ y)
        then LetIn y (expr_subst x v e1) (expr_subst x v e2)
        else e
    | Call e1 e2 => Call (expr_subst x v e1) (expr_subst x v e2)
    | Unit => Unit
    | Nat n => Nat n
    | Bool b => Bool b
    | BinOp op e1 e2 => BinOp op (expr_subst x v e1) (expr_subst x v e2)
    | If e0 e1 e2 => If (expr_subst x v e0) (expr_subst x v e1) (expr_subst x v e2)
    | Pair e1 e2 => Pair (expr_subst x v e1) (expr_subst x v e2)
    | Fst e => Fst (expr_subst x v e)
    | Snd e => Snd (expr_subst x v e)
    | Loc δ l => Loc δ l
    | Halloc e => Halloc (expr_subst x v e)
    | Salloc e => Salloc (expr_subst x v e)
    | Mask e => Mask (expr_subst x v e)
    | Load e => Load (expr_subst x v e)
    | Store e1 e2 => Store (expr_subst x v e1) (expr_subst x v e2)
    | Return e1 e2 => Return (expr_subst x v e1) (expr_subst x v e2)
    | Cont i K => Cont i (map (ectx_item_subst x v) K)
    end
  with ectx_item_subst (x : string) (v : val) (K : ectx_item) : ectx_item :=
         match K with
         | LetInCtx y e2 =>
             if decide (BNamed x ≠ y)
             then LetInCtx y (expr_subst x v e2)
             else K
         | BinOpRCtx op v1 => BinOpRCtx op (val_subst x v v1)
         | BinOpLCtx op e2 => BinOpLCtx op (expr_subst x v e2)
         | HallocCtx => HallocCtx
         | SallocCtx => SallocCtx
         | LoadCtx => LoadCtx
         | StoreLCtx e2 => StoreLCtx (expr_subst x v e2)
         | StoreRCtx v1 => StoreRCtx (val_subst x v v1)
         | MaskCtx => MaskCtx
         | CallLCtx e2 => CallLCtx (expr_subst x v e2)
         | CallRCtx v1 => CallRCtx (val_subst x v v1)
         | ReturnLCtx e2 => ReturnLCtx (expr_subst x v e2)
         | ReturnRCtx v1 => ReturnRCtx (val_subst x v v1)
         | PairLCtx e2 => PairLCtx (expr_subst x v e2)
         | PairRCtx v1 => PairRCtx (val_subst x v v1)
         | FstCtx => FstCtx
         | SndCtx => SndCtx
         | IfCtx e1 e2 => IfCtx (expr_subst x v e1) (expr_subst x v e2)
         end
  with val_subst (x : string) (v' : val) (v : val) : val :=
         match v with
         | LamV δ k y e =>
             LamV δ k y $
             if decide (BNamed x ≠ k ∧ BNamed x ≠ y)
             then expr_subst x v e
             else e
         | NatV n => NatV n
         | BoolV b => BoolV b
         | UnitV => UnitV
         | LocV δ l => LocV δ l
         | ContV i K => ContV i (map (ectx_item_subst x v) K)
         | PairV v1 v2 => PairV (val_subst x v v1) (val_subst x v v2)
         end.

  Notation ectx := (list ectx_item).
  
  Lemma expr_rect' (P : expr → Type) (Q : val → Type) :
    (∀ x : string, P (Var x))
    → (∀ (e : expr) δ k x, P e → P (Lam δ k x e))
    → (∀ (e1 : expr) x, P e1 → (∀ (e2 : expr), P e2 → P (LetIn x e1 e2)))
    → (∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Call e1 e2))
    → P Unit
    → (∀ n : nat, P (#n n))
    → (∀ b : bool, P (#♭ b))
    → (∀ (op : binop) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2))
    → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2))
    → (∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Pair e1 e2))
    → (∀ e : expr, P e → P (Fst e))
    → (∀ e : expr, P e → P (Snd e))
    → (∀ (l : loc) δ, P (Loc δ l))
    → (∀ e : expr, P e → P (Halloc e))
    → (∀ e : expr, P e → P (Salloc e))
    → (∀ e : expr, P e → P (Mask e))
    → (∀ e : expr, P e → P (Load e))
    → (∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Store e1 e2))
    → (∀ i,  P (Cont i []))
        
    → (∀ K e2 i, P (Cont i K) → P e2 → P (Cont i (CallLCtx e2 :: K)))
    → (∀ K v1 i, P (Cont i K) → Q v1 → P (Cont i (CallRCtx v1 :: K)))
    → (∀ K e2 i x, P (Cont i K) → P e2 → P (Cont i (LetInCtx x e2 :: K)))
    → (∀ K e2 i, P (Cont i K) → P e2 → P (Cont i (PairLCtx e2 :: K)))
    → (∀ K v1 i, P (Cont i K) → Q v1 → P (Cont i (PairRCtx v1 :: K)))
    → (∀ K op e2 i, P (Cont i K) → P e2 → P (Cont i (BinOpLCtx op e2 :: K)))
    → (∀ K op v1 i, P (Cont i K) → Q v1 → P (Cont i (BinOpRCtx op v1 :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (FstCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (SndCtx :: K)))
    → (∀ K e1 e2 i, P (Cont i K) → P e1 → P e2 → P (Cont i (IfCtx e1 e2 :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (HallocCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (SallocCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (LoadCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (MaskCtx :: K)))
    → (∀ K e2 i, P (Cont i K) → P e2 → P (Cont i (StoreLCtx e2 :: K)))
    → (∀ K v1 i, P (Cont i K) → Q v1 → P (Cont i (StoreRCtx v1 :: K)))
    → (∀ K e2 i, P (Cont i K) → P e2 → P (Cont i (ReturnLCtx e2 :: K)))
    → (∀ K v1 i, P (Cont i K) → Q v1 → P (Cont i (ReturnRCtx v1 :: K)))
    → (∀ e δ k x, P e → Q (LamV δ k x e))
    → (Q UnitV)
    → (∀ b, Q (NatV b))
    → (∀ b, Q (BoolV b))
    → (∀ v1 v2, Q v1 → Q v2 → Q (PairV v1 v2))
    → (∀ l δ, Q (LocV δ l))
    → (∀ K i, P (Cont i K) → Q (ContV i K))
    → (∀ i, Q (ContV i []))
    → (∀ K e2 i, Q (ContV i K) → P e2 → Q (ContV i (CallLCtx e2 :: K)))
    → (∀ K v1 i, Q (ContV i K) → Q v1 → Q (ContV i (CallRCtx v1 :: K)))
    → (∀ K e2 i x, Q (ContV i K) → P e2 → Q (ContV i (LetInCtx x e2 :: K)))
    → (∀ K e2 i, Q (ContV i K) → P e2 → Q (ContV i (PairLCtx e2 :: K)))
    → (∀ K v1 i, Q (ContV i K) → Q v1 → Q (ContV i (PairRCtx v1 :: K)))
    → (∀ K op e2 i, Q (ContV i K) → P e2 → Q (ContV i (BinOpLCtx op e2 :: K)))
    → (∀ K op v1 i, Q (ContV i K) → Q v1 → Q (ContV i (BinOpRCtx op v1 :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (FstCtx :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (SndCtx :: K)))
    → (∀ K e1 e2 i, Q (ContV i K) → P e1 → P e2 → Q (ContV i (IfCtx e1 e2 :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (HallocCtx :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (SallocCtx :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (LoadCtx :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (MaskCtx :: K)))
    → (∀ K e2 i, Q (ContV i K) → P e2 → Q (ContV i (StoreLCtx e2 :: K)))
    → (∀ K v1 i, Q (ContV i K) → Q v1 → Q (ContV i (StoreRCtx v1 :: K)))
    → (∀ K e2 i, Q (ContV i K) → P e2 → Q (ContV i (ReturnLCtx e2 :: K)))
    → (∀ K v1 i, Q (ContV i K) → Q v1 → Q (ContV i (ReturnRCtx v1 :: K)))
    → (∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Return e1 e2))
    → ∀ e : expr, P e.
  Proof.
    intros Hvar HLam HLetIn Happ Hunit Hnat Hbool Hbinop Hif Hpair Hfst Hsnd
      Hloc Hhalloc Hsalloc Hmask Hload
      Hstore
      HKnil HAppLCtx HAppRCtx HLetInCtx HPairLCtx HPairRCtx
      HBinOpLCtx HBinOpRCtx HFstCtx HSndCtx HIfCtx
      HHallocCtx HSallocCtx HLoadCtx HMaskCtx HStoreLCtx HStoreRCtx
      HThrowLCtx HThrowRCtx
      HLamV HUnitV HNatV HBoolV HPairV HLocV
      HContV
      HKnilV HAppLCtxV HAppRCtxV HLetInCtxV
      HPairLCtxV HPairRCtxV HBinOpLCtxV
      HBinOpRCtxV HFstCtxV HSndCtxV HIfCtxV
      HHallocCtxV HSallocCtxV HLoadCtxV HMaskCtxV HStoreLCtxV HStoreRCtxV
      HThrowLCtxV HThrowRCtxV
      Hthrow e.
    refine (
        (fix fx (e : expr) {struct e} :=
           match e as u return (* F u → *) P u with
           | Var x => Hvar _
           | Lam δ k x e => HLam _ δ k x (fx e)
           | LetIn x e1 e2 => HLetIn _ x (fx e1) _ (fx e2)
           | Call e1 e2 => Happ _ (fx e1) _ (fx e2)
           | Unit => Hunit
           | Nat n => Hnat _
           | Bool b => Hbool _
           | BinOp op e1 e2 => Hbinop _ _ (fx e1) _ (fx e2)
           | If e0 e1 e2 => Hif _ (fx e0) _ (fx e1) _ (fx e2)
           | Pair e1 e2 => Hpair _ (fx e1) _ (fx e2)
           | Fst e => Hfst _ (fx e)
           | Snd e => Hsnd _ (fx e)
           | Loc δ l => Hloc _ _
           | Halloc e => Hhalloc _ (fx e)
           | Salloc e => Hsalloc _ (fx e)
           | Mask e => Hmask _ (fx e)
           | Load e => Hload _ (fx e)
           | Store e1 e2 => Hstore _ (fx e1) _ (fx e2)
           | Cont i K =>
               (fix gx (K : ectx) {struct K} :=
                  let HX :=
                    fix hx (v : val) {struct v} :=
                      match v as u return Q u with
                      | LamV δ k x e => HLamV _ _ _ _ (fx e)
                      | UnitV => HUnitV
                      | NatV n => HNatV n
                      | BoolV b => HBoolV b
                      | PairV v1 v2 => HPairV _ _ (hx v1) (hx v2)
                      | LocV δ l => HLocV l δ
                      | ContV j K'' =>
                          (fix gx' (K : ectx) {struct K} :=
                             match K as u return Q (ContV j u) with
                             | nil => HKnilV _
                             | (CallLCtx e2) :: K' => HAppLCtxV _ _ _ (gx' K') (fx e2)
                             | (CallRCtx v1) :: K' => HAppRCtxV _ _ _ (gx' K') (hx v1)
                             | (LetInCtx x e2) :: K' => HLetInCtxV _ _ _ _ (gx' K') (fx e2)
                             | (PairLCtx e2) :: K' => HPairLCtxV _ _ _ (gx' K') (fx e2)
                             | (PairRCtx v1) :: K' => HPairRCtxV _ _ _ (gx' K') (hx v1)
                             | (BinOpLCtx op e2) :: K' => HBinOpLCtxV _ _ _ _ (gx' K') (fx e2)
                             | (BinOpRCtx op v1) :: K' => HBinOpRCtxV _ _ _ _ (gx' K') (hx v1)
                             | (FstCtx) :: K' => HFstCtxV _ _ (gx' K')
                             | (SndCtx) :: K' => HSndCtxV _ _ (gx' K')
                             | (IfCtx e1 e2) :: K' => HIfCtxV _ _ _ _ (gx' K') (fx e1) (fx e2)
                             | (HallocCtx) :: K' => HHallocCtxV _ _ (gx' K')
                             | (SallocCtx) :: K' => HSallocCtxV _ _ (gx' K')
                             | (LoadCtx) :: K' => HLoadCtxV _ _ (gx' K')
                             | (MaskCtx) :: K' => HMaskCtxV _ _ (gx' K')
                             | (StoreLCtx e2) :: K' => HStoreLCtxV _ _ _ (gx' K') (fx e2)
                             | (StoreRCtx v1) :: K' => HStoreRCtxV _ _ _ (gx' K') (hx v1)
                             | (ReturnLCtx e2) :: K' => HThrowLCtxV _ _ _ (gx' K') (fx e2)
                             | (ReturnRCtx v1) :: K' => HThrowRCtxV _ _ _ (gx' K') (hx v1)
                             end) K''
                      end
                  in
                  match K as u return P (Cont i u) with
                  | nil => HKnil _
                  | (CallLCtx e2) :: K' => HAppLCtx _ _ _ (gx K') (fx e2)
                  | (CallRCtx v1) :: K' => HAppRCtx _ _ _ (gx K') (HX v1)
                  | (LetInCtx x e2) :: K' => HLetInCtx _ _ _ _ (gx K') (fx e2)
                  | (PairLCtx e2) :: K' => HPairLCtx _ _ _ (gx K') (fx e2)
                  | (PairRCtx v1) :: K' => HPairRCtx _ _ _ (gx K') (HX v1)
                  | (BinOpLCtx op e2) :: K' => HBinOpLCtx _ _ _ _ (gx K') (fx e2)
                  | (BinOpRCtx op v1) :: K' => HBinOpRCtx _ _ _ _ (gx K') (HX v1)
                  | (FstCtx) :: K' => HFstCtx _ _ (gx K')
                  | (SndCtx) :: K' => HSndCtx _ _ (gx K')
                  | (IfCtx e1 e2) :: K' => HIfCtx _ _ _ _ (gx K') (fx e1) (fx e2)
                  | (HallocCtx) :: K' => HHallocCtx _ _ (gx K')
                  | (SallocCtx) :: K' => HSallocCtx _ _ (gx K')
                  | (LoadCtx) :: K' => HLoadCtx _ _ (gx K')
                  | (MaskCtx) :: K' => HMaskCtx _ _ (gx K')
                  | (StoreLCtx e2) :: K' => HStoreLCtx _ _ _ (gx K') (fx e2)
                  | (StoreRCtx v1) :: K' => HStoreRCtx _ _ _ (gx K') (HX v1)
                  | (ReturnLCtx e2) :: K' => HThrowLCtx _ _ _ (gx K') (fx e2)
                  | (ReturnRCtx v1) :: K' => HThrowRCtx _ _ _ (gx K') (HX v1)
                  end) K
           | Return e1 e2 => Hthrow _ (fx e1) _ (fx e2)
           end) e).
  Qed.

  Instance expr_dec_eq : EqDecision expr.
  Proof.
    intros e.
    apply (expr_rect' (λ e, ∀ e' : expr, Decision (e = e'))
             (λ w, ∀ v, Decision (w = v))); intros;
      match goal with
        |- Decision (?A = ?B) => destruct B
      end;
      try match goal with
          |- Decision (Cont _ ?A = Cont _ ?B) => destruct B as [|[]]
        end;
      try match goal with
        | |- Decision (ContV _ (_ :: _) = ContV _ ?B) => destruct B as [|[]]
        | |- Decision (ContV _ [] = ContV _ ?B) => destruct B as [|[]]
        end; try (right; inversion 1; fail).
    all: try match goal with
           | |- Decision (?A = ?A) => left; trivial
           | |- Decision (?A ?B = ?A ?C) => destruct (decide (B = C));
                                          [| right; inversion 1; tauto]; subst; left; eauto
           | |- Decision (?A ?B1 ?B2 = ?A ?C1 ?C2) =>
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               subst; left; eauto
           | |- Decision (?A ?B1 ?B2 ?B3 = ?A ?C1 ?C2 ?C3) =>
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               destruct (decide (B3 = C3)); [| right; inversion 1; tauto];
               subst; left; eauto
           | |- Decision (?A ?B1 ?B2 ?B3 = ?A ?C1 ?C2 ?C3) =>
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               destruct (decide (B3 = C3)); [| right; inversion 1; tauto];
               subst; left; eauto
           | |- Decision (?A ?B1 ?B2 ?B3 ?B4 = ?A ?C1 ?C2 ?C3 ?C4) =>
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               destruct (decide (B3 = C3)); [| right; inversion 1; tauto];
               destruct (decide (B4 = C4)); [| right; inversion 1; tauto];
               subst; left; eauto
           end.
    all: try match goal with
           | |- Decision (Cont ?i (?A :: ?K1) = Cont ?i0 (?A :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (Cont i K1 = Cont i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto]; subst; left; eauto
           | |- Decision (Cont ?i (?A ?B :: ?K1) = Cont ?i0 (?A ?C :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (Cont i K1 = Cont i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto];
               destruct (decide (B = C)); [| right; inversion 1; tauto];
               subst; left; eauto
           | |- Decision (Cont ?i (?A ?B1 ?B2 :: ?K1) = Cont ?i0 (?A ?C1 ?C2 :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (Cont i K1 = Cont i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto];
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               subst; left; eauto
           end.
    all: try match goal with
           | |- Decision (ContV ?i (?A :: ?K1) = ContV ?i0 (?A :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (ContV i K1 = ContV i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto]; subst; left; eauto
           | |- Decision (ContV ?i (?A ?B :: ?K1) = ContV ?i0 (?A ?C :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (ContV i K1 = ContV i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto];
               destruct (decide (B = C)); [| right; inversion 1; tauto];
               subst; left; eauto
           | |- Decision (ContV ?i (?A ?B1 ?B2 :: ?K1) = ContV ?i0 (?A ?C1 ?C2 :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (ContV i K1 = ContV i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto];
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               subst; left; eauto
           end.
    match goal with
    | |- Decision (ContV ?i ?K1 = ContV ?i0 ?K2) =>
        destruct (decide (Cont i K1 = Cont i0 K2)) as [Hf|];
        [inversion Hf| right; inversion 1; subst; tauto];
        subst; left; eauto
    end.
  Qed.

  (*** Operational Semantics *)


  Fixpoint shift_val (v : val) (off : Z) : val :=
    match v with
    | LamV (local i) k x e => LamV (local (i + off)) k x e (* e is only shifted once λe is invoked *)
    | LocV (local i) l => LocV (local (i + off)) l
    | ContV i K => ContV (i + off) K (* no need to shift K, since invoking it pops the stack to correct shape *)
    | PairV v1 v2 => PairV (shift_val v1 off) (shift_val v2 off)
    | _ => v
    end.

  Fixpoint shift_expr (e : expr) (off : Z) : expr :=
    match e with
    | Var x => Var x
    | Lam (local i) k x e => Lam (local (i + off)) k x e
    | Lam δ k x e => Lam δ k x e
    | LetIn x e1 e2 => LetIn x (shift_expr e1 off) (shift_expr e2 off)
    | Call e1 e2 => Call (shift_expr e1 off) (shift_expr e2 off)
    | Unit => Unit
    | Nat n => Nat n
    | Bool b => Bool b
    | BinOp op e1 e2 => BinOp op (shift_expr e1 off) (shift_expr e2 off)
    | If e0 e1 e2 => If (shift_expr e0 off) (shift_expr e1 off) (shift_expr e2 off)
    | Pair e1 e2 => Pair (shift_expr e1 off) (shift_expr e2 off)
    | Fst e => Fst (shift_expr e off)
    | Snd e => Snd (shift_expr e off)
    | Loc (local i) l => Loc (local (i + off)) l
    | Loc δ l => Loc δ l
    | Halloc e => Halloc (shift_expr e off)
    | Salloc e => Salloc (shift_expr e off)
    | Mask e => Mask (shift_expr e off)
    | Load e => Load (shift_expr e off)
    | Store e1 e2 => Store (shift_expr e1 off) (shift_expr e2 off)
    | Return e1 e2 => Return (shift_expr e1 off) (shift_expr e2 off)
    | Cont i K => Cont (i + off) K
    end.

  Lemma shift_of_val v off :
    of_val (shift_val v off) = shift_expr (of_val v) off.
  Proof.
    induction v;auto.
    - destruct δ;simpl;auto.
    - destruct δ;simpl;auto.
    - rewrite /= IHv1 IHv2 //.
  Qed.

  Definition heap : Type := gmap loc val.
  Definition stack : Type := list (gmap loc val).
  Definition state : Type := heap * stack.
  Definition observation : Type := Empty_set.

  Definition heap_of (σ : state) : heap := fst σ.
  Definition stack_of (σ : state) : stack := snd σ.
  
  Inductive scope_tag : tag -> Prop :=
  | borrowScope : scope_tag borrow
  | globalScope : scope_tag global
  | localScope i : i <= 0 -> scope_tag (local i).

  Inductive permanent : val -> Prop :=
  | lamPerm k x e : permanent (LamV global k x e)
  | natPerm n : permanent (NatV n)
  | boolPerm b : permanent (BoolV b)
  | unitPerm : permanent UnitV
  | locPerm l : permanent (LocV global l)
  | pairPerm v1 v2 : permanent v1 -> permanent v2 -> permanent (PairV v1 v2).

  Inductive scope : val -> Z -> Prop :=
  | permScope v n : permanent v -> scope v n
  | locScope δ l n : scope_tag δ -> scope (LocV δ l) n
  | lamScope δ k x e n : scope_tag δ -> scope (LamV δ k x e) n
  | contScope i K j : i <= j -> scope (ContV i K) j.

  Inductive heap_tag : tag -> Prop :=
  | borrowHeap : heap_tag borrow
  | globalHeap : heap_tag global.

  Definition insert_heap (l : loc) (v : val) (σ : state) := let '(h,s) := σ in (<[l:=v]>h,s).

  Definition insert_stack (l : loc) (i : nat) (v : val) (σ : state) :=
    let '(h,s) := σ in
    match s !! ((length s) - 1 - i) with
    | Some σi => (h,<[(length s) - 1 - i:=<[l:=v]>σi]>s)
    | None => σ
    end.

  Definition insert_state (li : loc * option nat) (v : val) (σ : state) :=
    match li with
    | (l,Some i) => insert_stack l i v σ
    | (l,None) => insert_heap l v σ
    end.

  Global Instance insert_state_Insert : Insert (loc * option nat) val state := insert_state.

  Definition lookup_heap (l : loc) (σ : state) := heap_of σ !! l.
  Definition lookup_stack (l : loc) (i : nat) (σ : state) := s ← stack_of σ !! ((length (stack_of σ)) - 1 - i); s !! l.

  Definition lookup_state (li : loc * option nat) (σ : state) :=
    match li with
    | (l,Some i) => lookup_stack l i σ
    | (l,None) => lookup_heap l σ
    end.

  Global Instance lookup_state_Lookup : Lookup (loc * option nat) val state := lookup_state.

  Notation "<[ l @@ := v ]>" := (insert (l,None) v)
                                  (at level 5, right associativity, format "<[ l @@ := v ]>") : stdpp_scope.
  Notation "<[ i @ l := v ]>" := (insert (l,Some i) v)
                                   (at level 5, right associativity, format "<[ i @ l := v ]>") : stdpp_scope.
  Notation "[[ σ @@ ]] !! l" := (lookup (l,None) σ) (at level 20) : stdpp_scope.
  Notation "[[ σ @ i ]] !! l" := (lookup (l,Some i) σ) (at level 20, format "[[ σ @ i ]] !! l") : stdpp_scope.

  Lemma not_elem_of_heap_dom l σ :
    l ∉ dom (heap_of σ) <-> [[σ@@]] !! l = None.
  Proof.
    destruct σ. rewrite /= /lookup_heap /=.
    apply not_elem_of_dom.
  Qed.

  Lemma not_elem_of_stack_dom l σ (s : gmap loc val) i :
    (stack_of σ) !! (length (stack_of σ) - 1 - i) = Some s ->
    l ∉ dom s <-> [[σ @ i]] !! l = None.
  Proof.
    destruct σ. rewrite /= /lookup_stack /=.
    intros ->. apply not_elem_of_dom.
  Qed.

  
  Definition push_stack (s : stack) : stack := s ++ [∅].
  Definition push (σ : state) : state := let '(h,s) := σ in (h,push_stack s).

  Fixpoint pushN_stack (s : stack) (n : nat) : stack :=
    match n with
    | 0 => s
    | S m => pushN_stack (push_stack s) m
    end.
  Definition pushN (σ : state) (n : nat) : state := let '(h,s) := σ in (h,pushN_stack s n).

  Definition pop_stack (s : stack) : stack :=
    match reverse s with
    | [] => s
    | sn :: s' => reverse s'
    end.
  Definition pop (σ : state) : state := let '(h,s) := σ in (h,pop_stack s).

  Fixpoint popN_stack (s : stack) (n : nat) : stack :=
    match n with
    | 0 => s
    | S m => popN_stack (pop_stack s) m
    end.
  Definition popN (σ : state) (n : nat) : state := let '(h,s) := σ in (h,popN_stack s n).
  
  Lemma pop_stack_snoc s sn :
    pop_stack (s ++ [sn]) = s.
  Proof. rewrite /pop_stack /= reverse_snoc reverse_involutive //. Qed.
  Lemma pop_snoc σ s sn :
    stack_of σ = s ++ [sn] ->
    pop σ = (heap_of σ, s).
  Proof. intros; destruct σ;simpl in *;subst. f_equiv. apply pop_stack_snoc. Qed.

  Lemma push_pushN_stack s : push_stack s = pushN_stack s 1.
  Proof. auto. Qed.
  Lemma pop_popN_stack s : pop_stack s = popN_stack s 1.
  Proof. auto. Qed.

  Lemma pushN_stack_spec s n :
    pushN_stack s n = s ++ repeat ∅ n.
  Proof.
    revert s; induction n; intros s; simpl;eauto.
    - rewrite app_nil_r. auto.
    - unfold push_stack. rewrite IHn.
      rewrite -app_assoc cons_middle //.
  Qed.

  Lemma popN_stack_spec s n l m :
    length l = m ->
    popN_stack (s ++ l) (n + m) = popN_stack s n.
  Proof.
    revert s n m; induction l using rev_ind; intros s n m Hl; simpl in *;eauto.
    - subst. simpl. rewrite app_nil_r;auto.
    - rewrite app_length in Hl. rewrite Nat.add_1_r in Hl.
      destruct m;[done|].
      rewrite app_assoc.
      assert (n + S m = S (n + m)) as ->;[lia|].
      simpl. rewrite pop_stack_snoc.
      apply IHl. auto.
  Qed.
  Lemma popN_stack_spec_derived s l n :
    length l = n ->
    popN_stack (s ++ l) n = s.
  Proof.
    intros Hlen. assert (n = 0 + n) as ->;[lia|].
    apply popN_stack_spec. auto.
  Qed.
  Lemma popN_stack_app s l :
    popN_stack (s ++ l) (length l) = s.
  Proof. apply popN_stack_spec_derived. auto. Qed.
  Lemma popN_stack_empty s :
    popN_stack s (length s) = [].
  Proof. rewrite <- (app_nil_l s). apply popN_stack_spec_derived;auto. Qed.    
  
  Lemma push_popN_stack s n :
    popN_stack (pushN_stack s n) n = s.
  Proof.
    rewrite pushN_stack_spec.
    rewrite popN_stack_spec_derived//.
    apply repeat_length.
  Qed.
  Lemma push_pop_stack s :
    pop_stack (push_stack s) = s.
  Proof.
    rewrite pop_popN_stack push_pushN_stack.
    apply push_popN_stack.
  Qed.

  Definition binop_eval (op : binop) (v v' : val) : option val :=
    match v with
    | (#nv a) =>
        match v' with
        | (#nv b) =>
            match op with
            | Add => Some (#nv (a + b))
            | Sub => Some (#nv (a - b))
            | Eq => Some (#♭v (bool_decide (a = b)))
            | Le => Some (#♭v (bool_decide (a ≤ b)))
            | Lt => Some (#♭v (bool_decide (a < b)))
            end
        | _ => None
        end
    | _ => None
    end.


  Definition subst' (mx : binder) (v : val) : expr → expr :=
    match mx with BNamed x => expr_subst x v | BAnon => id end.

  Inductive head_step : list ectx_item -> expr -> state -> list observation -> expr -> state -> list expr -> RedMode -> Prop :=
  (** Local Lam-β *)
  | LamBetaLocalS K k x e1 i e2 v2 σ e1' v2' :
    to_val e2 = Some v2 ->
    scope_tag (local i) ->
    shift_val v2 (-1) = v2' ->
    shift_expr e1 (i - 1) = e1' ->
    head_step K (Call (Lam (local i) k x e1) e2) σ []
      (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1'))) (push σ) [] CaptureMode

  (** Global Lam-β *)
  | LamBetaGlobalS K k x e1 e2 v2 σ v2' :
    to_val e2 = Some v2 ->
    shift_val v2 (-1) = v2' ->
    head_step K (Call (Lam global k x e1) e2) σ []
      (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1))) (push σ) [] CaptureMode

  (** Return *)
  | ReturnS K K' i e e' v σ :
    to_val e = Some v ->
    shift_expr e i = e' ->
    (i <= 0)%Z ->
    length (stack_of σ) >= Z.abs_nat i ->
    head_step K (Return (Cont i K') e) σ [] (foldl (flip fill_item) e' K') (popN σ (Z.abs_nat i)) [] ThrowMode

  (** zeta *)
  | ZetaS K x e1 e2 v1 σ :
    to_val e1 = Some v1 ->
    head_step K (LetIn x e1 e2) σ [] (subst' x v1 e2) σ [] NormalMode

  (** Products *)
  | FstS K e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step K (Fst (Pair e1 e2)) σ [] e1 σ [] NormalMode
  | SndS K e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step K (Snd (Pair e1 e2)) σ [] e2 σ [] NormalMode

  (** BinOp *)
  | BinOpS K op e1 e2 v1 v2 w σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    binop_eval op v1 v2 = Some w →
    head_step K (BinOp op e1 e2) σ [] (of_val w) σ [] NormalMode

  (** Allocation *)
  | HallocS K e v σ l :
    to_val e = Some v ->
    permanent v ->
    [[σ @@]] !! l = None ->
    head_step K (Halloc e) σ [] (Loc global l) (<[l@@:=v]>σ) [] NormalMode

  | SallocS K e v σ l :
    to_val e = Some v ->
    scope v 0 ->
    [[σ @ 0]] !! l = None ->
    head_step K (Salloc e) σ [] (Loc (local 0) l) (<[0@l:=v]>σ) [] NormalMode

  (** Loading *)
  | LoadHeapS K v l δ σ :
    [[σ @@]] !! l = Some v ->
    heap_tag δ ->
    head_step K (Load (Loc δ l)) σ [] (of_val v) σ [] NormalMode

  | LoadStackS K v v' l i σ :
    [[σ @ (Z.abs_nat i)]] !! l = Some v ->
    scope_tag (local i) ->
    shift_val v i = v' ->
    head_step K (Load (Loc (local i) l)) σ [] (of_val v') σ [] NormalMode

  (** Storing *)
  | StoreHeapS K e v l δ σ :
    to_val e = Some v ->
    permanent v ->
    heap_tag δ ->
    is_Some ([[σ @@]] !! l) ->
    head_step K (Store (Loc δ l) e) σ [] Unit (<[l@@:=v]>σ) [] NormalMode

  | StoreStackS K e v v' l j i σ :
    i = (Z.abs_nat j) ->
    to_val e = Some v ->
    scope v j ->
    shift_val v i = v' ->
    is_Some ([[σ @ i]] !! l) ->
    head_step K (Store (Loc (local j) l) e) σ [] Unit (<[i@l:=v]>σ) [] NormalMode

  (** Downgrade Heap Location *)
  | MaskS K l σ :
    head_step K (Mask (Loc global l)) σ [] (Loc borrow l) σ [] NormalMode

  (** If then else *)
  | IfFalse K e1 e2 σ :
    head_step K (If (#♭ false) e1 e2) σ [] e2 σ [] NormalMode
  | IfTrue K e1 e2 σ :
    head_step K (If (#♭ true) e1 e2) σ [] e1 σ [] NormalMode

  .

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck K e1 σ1 κ e2 σ2 ef rm :
    head_step K e1 σ1 κ e2 σ2 ef rm → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val K Ki e σ1 κ e2 σ2 ef rm :
    head_step K (fill_item Ki e) σ1 κ e2 σ2 ef rm → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
      repeat match goal with
        | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
        end; auto.
  Qed.

  Lemma red_mode_det K e1 σ1 κ e2 σ2 efs rm :
    head_step K e1 σ1 κ e2 σ2 efs rm →
    ∀ K' σ1' κ' e2' σ2' efs' rm',
      head_step K' e1 σ1' κ' e2' σ2' efs' rm' → rm' = rm.
  Proof. by destruct 1; intros ??????; inversion 1. Qed.           

  Definition capture K e :=
    match e with
    | Call (Lam global k x e1) e2 =>
        match to_val e2 with
        | Some v2 => 
            let v2' := shift_val v2 (-1) in
            Some (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1)))
        | None => None
        end
    | Call (Lam (local i) k x e1) e2 =>
        if (i <=? 0)%Z then
          match to_val e2 with
          | Some v2 =>
              let v2' := shift_val v2 (-1) in
              let e1' := shift_expr e1 (i - 1) in
              Some (Return (Cont (-1) K) (subst' k (ContV (-1) K) (subst' x v2' e1')))
          | None => None
          end
        else None
    | _ => None
    end.

  Lemma scope_tag_local_leb i :
    scope_tag (local i) ->
    (i <=? 0)%Z = true.
  Proof. inversion 1;lia. Qed.
  
  Lemma ectxi_capture_captures K e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs CaptureMode →
    capture K e1 = Some e2.
  Proof.
    inversion 1; eauto.
    - simplify_eq. rewrite /= scope_tag_local_leb /= //.
      simplify_option_eq. auto.
    - simplify_eq. simpl. simplify_option_eq. auto.
  Qed.

  Lemma ectxi_normal_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs NormalMode →
    head_step K' e1 σ1 κ e2 σ2 efs NormalMode.
  Proof.
    inversion 1; by (econstructor;eauto).
  Qed.

  Lemma ectxi_capture_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs CaptureMode →
    ∃ e2', capture K' e1 = Some e2' ∧
             head_step K' e1 σ1 κ e2' σ2 efs CaptureMode.
  Proof.
    inversion 1; subst; simpl; eauto using head_step.
    - simplify_option_eq. rewrite /= scope_tag_local_leb /= //.
      eauto using head_step.
    - simplify_option_eq. eauto using head_step.
  Qed.

  Lemma ectxi_throw_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs ThrowMode →
    head_step K' e1 σ1 κ e2 σ2 efs ThrowMode.
  Proof. inversion 1; econstructor; eauto. Qed.

  
  Lemma halloc_fresh K e v σ :
    let l := fresh (dom (heap_of σ)) in
    to_val e = Some v →
    permanent v ->
    head_step K (Halloc e) σ [] (Loc global l) (<[l@@:=v]>σ) [] NormalMode.
  Proof. intros; apply HallocS;auto. apply not_elem_of_dom,is_fresh. Qed.

  Lemma salloc_fresh K e v σ s :
    let l := fresh (dom s) in
    stack_of σ !! (length (stack_of σ) - 1) = Some s ->
    to_val e = Some v →
    scope v 0 ->
    head_step K (Salloc e) σ [] (Loc (local 0) l) (<[0 @ l:=v]>σ) [] NormalMode.
  Proof.
    intros; apply SallocS;auto.
    eapply not_elem_of_stack_dom;[|eapply is_fresh]. rewrite Nat.sub_0_r //.
  Qed.

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprC := leibnizO expr.
End lang.

(** Language *)
Program Instance stack_lambda_ectxi_lang :
  CCEctxiLanguage
    (lang.expr) lang.val lang.ectx_item lang.state lang.observation :=
  {|
    of_val := lang.of_val;
    to_val := lang.to_val;
    fill_item := lang.fill_item;
    head_step := lang.head_step;
    capture := lang.capture
  |}.
Solve Obligations with simpl; eauto using lang.to_of_val, lang.of_to_val,
  lang.val_stuck, lang.fill_item_val, lang.fill_item_no_val_inj,
  lang.head_ctx_step_val, lang.red_mode_det, lang.ectxi_capture_captures,
  lang.ectxi_normal_reduciblity, lang.ectxi_throw_reduciblity,
  lang.ectxi_capture_reduciblity.

Canonical Structure lang := CC_ectx_lang (lang.expr).

Export lang.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Halloc e => is_Some (to_val e)
  | Salloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
Lemma is_atomic_sub_values e : is_atomic e → sub_values e.
Proof.
  destruct e; inversion 1; simpl; apply ectxi_language_sub_values;
    intros [] ?; inversion 1; subst; simpl in *; tauto.
Qed.
Lemma is_atomic_correct e : is_atomic e → Atomic StronglyAtomic e.
Proof.
  intros ?; apply ectx_language_atomic; simpl.
  - destruct 1; simpl; try done; rewrite ?to_of_val; eauto.
  - apply ectxi_language_sub_values => Ki e' Heq; subst; simpl in *.
    destruct Ki; naive_solver.
Qed.
Lemma is_atomic_normal e : is_atomic e → is_normal e.
Proof. by destruct e; inversion 1; intros ????; inversion 1; simpl. Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
  rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Ltac solve_is_atomic :=
  simpl; repeat split; rewrite ?to_of_val; eapply mk_is_Some; fast_done.

#[export] Hint Extern 0 (language.atomic _) => solve_atomic : core.
#[export] Hint Extern 0 (language.atomic _) => solve_atomic : typeclass_instances.
#[export] Hint Extern 0 (is_atomic _) => solve_is_atomic : core.
#[export] Hint Extern 0 (is_atomic _) => solve_is_atomic : typeclass_instances.

#[export] Hint Extern 1 (IntoVal _ _) =>
       rewrite /IntoVal /=; repeat rewrite to_of_val /= : core.

#[export] Hint Extern 1 (IntoVal _ _) =>
       rewrite /IntoVal /=; repeat rewrite to_of_val /=: typeclass_instances.

#[export] Hint Extern 1 (AsVal _) =>
       rewrite /AsVal /=; repeat rewrite to_of_val /= : core.

#[export] Hint Extern 1 (AsVal _) =>
       rewrite /AsVal /=; repeat rewrite to_of_val /= : typeclass_instances.
