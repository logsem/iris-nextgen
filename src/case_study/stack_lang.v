Require Export Logic.FunctionalExtensionality.
From iris.program_logic Require Import language.
From nextgen.case_study.program_logic Require Import CC_ectx_lifting CC_ectxi_language.
From nextgen.case_study Require Import prelude.
From stdpp Require Import binders strings gmap.

Definition loc := positive.

Inductive binop := Add | Sub | Eq | Le | Lt.

Global Instance binop_dec_eq : EqDecision binop.
Proof. solve_decision. Defined.

Inductive tag :=
| global : tag
| borrow : tag
| local : nat -> tag.

Global Instance tag_dec_eq : EqDecision tag.
Proof. solve_decision. Defined.

Module lang.

  (*** Syntax *)
  
  Inductive expr :=
  (* Variable Bindings *)
  | Var (x : string)
  | Rec (δ : tag) (k f x : binder) (e : expr)
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
  | Cont (i : nat) (K : list ectx_item)
  | Call (e1 : expr) (e2 : expr)
  | Return (e1 : expr) (e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (x : binder) (e1 : expr) (e2 : expr)
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
  | InjLCtx
  | InjRCtx
  | CaseCtx (x : binder) (e1 : expr) (e2 : expr)


  with val :=
  | RecV (δ : tag) (k f x : binder) (e : expr)
  | NatV (n : nat)
  | BoolV (b : bool)
  | UnitV
  | LocV (δ : tag) (l : loc)
  | ContV (i : nat) (K : list ectx_item)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

  Bind Scope expr_scope with expr.
  Bind Scope val_scope with val.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Rec δ k f x e => Some (RecV δ k f x e)
    | Nat n => Some (NatV n)
    | Bool b => Some (BoolV b)
    | Unit => Some UnitV
    | Loc δ l => Some (LocV δ l)
    | Cont i K => Some (ContV i K)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => v ← to_val e; Some (InjLV v)
    | InjR e => v ← to_val e; Some (InjRV v) 
    | _ => None
  end.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | RecV δ k f x e => Rec δ k f x e
    | NatV n => Nat n
    | BoolV b => Bool b
    | UnitV => Unit
    | LocV δ l => Loc δ l
    | ContV i K => Cont i K
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    end.

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | CallLCtx e2 => Call e e2
    | CallRCtx v1 => Call (of_val v1) e
    | LetInCtx x e2 => LetIn x e e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx x e1 e2 => Case e x e1 e2
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
  Proof. induction v;eauto. all: by simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
  Proof. revert v; induction e =>v Hv; simplify_option_eq;auto. all: f_equiv;auto. Qed.

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
    | Rec δ k f z e =>
        if decide (BNamed x = k) then Rec δ (BNamed y) f z (expr_rename x y e)
        else if decide (BNamed x = f) then Rec δ k (BNamed y) z (expr_rename x y e)
             else if decide (BNamed x = z) then Rec δ k f (BNamed y) (expr_rename x y e)
             else Rec δ k f z (expr_rename x y e)
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
    | InjL e => InjL (expr_rename x y e)
    | InjR e => InjR (expr_rename x y e)
    | Case e1 z1 e2 e3 => 
        if decide (BNamed x = z1) then Case (expr_rename x y e1) (BNamed y) (expr_rename x y e2) (expr_rename x y e3)
        else Case (expr_rename x y e1) z1 (expr_rename x y e2) (expr_rename x y e3)
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
         | InjLCtx => InjLCtx
         | InjRCtx => InjRCtx
         | CaseCtx z1 e1 e2 => if decide (BNamed x = z1) then CaseCtx (BNamed y) (expr_rename x y e1) (expr_rename x y e2)
                              else CaseCtx z1 (expr_rename x y e1) (expr_rename x y e2)
         | IfCtx e1 e2 => IfCtx (expr_rename x y e1) (expr_rename x y e2)
         end
  with val_rename (x y : string) (v : val) : val :=
         match v with
         | RecV δ k f z e =>
             if decide (BNamed x = k) then RecV δ (BNamed y) f z e
             else if decide (BNamed x = f) then RecV δ k (BNamed y) z e
                  else if decide (BNamed x = z) then RecV δ k f (BNamed y) e
                       else RecV δ k f z (expr_rename x y e)
         | NatV n => NatV n
         | BoolV b => BoolV b
         | UnitV => UnitV
         | LocV δ l => LocV δ l
         | ContV i K => ContV i (map (ectx_item_rename x y) K)
         | PairV v1 v2 => PairV (val_rename x y v1) (val_rename x y v2)
         | InjLV v => InjLV (val_rename x y v)
         | InjRV v => InjRV (val_rename x y v)
         end.

  (** Substitution, replaces occurrences of [x] in [e] with [v]. *)
  Fixpoint expr_subst (x : string) (v : val) (e : expr) : expr :=
    match e with
    | Var y => if decide (x = y) then of_val v else Var y
    | Rec δ k f y e =>
        Rec δ k f y $
          if decide (BNamed x ≠ k ∧ BNamed x ≠ f ∧ BNamed x ≠ y)
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
    | InjL e => InjL (expr_subst x v e)
    | InjR e => InjR (expr_subst x v e)
    | Case e0 y e1 e2 =>
        if decide (BNamed x ≠ y)
        then Case (expr_subst x v e0) y (expr_subst x v e1) (expr_subst x v e2)
        else e
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
         | InjLCtx => InjLCtx
         | InjRCtx => InjRCtx
         | CaseCtx y e1 e2 =>
             if decide (BNamed x ≠ y)
             then CaseCtx y (expr_subst x v e1) (expr_subst x v e2)
             else K
         | IfCtx e1 e2 => IfCtx (expr_subst x v e1) (expr_subst x v e2)
         end
  with val_subst (x : string) (v' : val) (v : val) : val := v
         (* match v with *)
         (* | RecV δ k f y e => *)
         (*     RecV δ k f y $ *)
         (*     if decide (BNamed x ≠ k ∧ BNamed x ≠ f ∧ BNamed x ≠ y) *)
         (*     then expr_subst x v e *)
         (*     else e *)
         (* | NatV n => NatV n *)
         (* | BoolV b => BoolV b *)
         (* | UnitV => UnitV *)
         (* | LocV δ l => LocV δ l *)
         (* | ContV i K => ContV i (map (ectx_item_subst x v) K) *)
         (* | PairV v1 v2 => PairV (val_subst x v v1) (val_subst x v v2) *)
         (* | InjLV v1 => InjLV (val_subst x v v1) *)
         (* | InjRV v1 => InjRV (val_subst x v v1) *)
         (* end *).

  Notation ectx := (list ectx_item).
  
  Lemma expr_rect' (P : expr → Type) (Q : val → Type) :
    (∀ x : string, P (Var x))
    → (∀ (e : expr) δ k f x, P e → P (Rec δ k f x e))
    → (∀ (e1 : expr) x, P e1 → (∀ (e2 : expr), P e2 → P (LetIn x e1 e2)))
    → (∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Call e1 e2))
    → P Unit
    → (∀ n : nat, P (#n n))
    → (∀ b : bool, P (#♭ b))
    → (∀ (op : binop) (e1 : expr), P e1 → ∀ e2 : expr, P e2 → P (BinOp op e1 e2))
    → (∀ e0 : expr, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (If e0 e1 e2))
    → (∀ (e0 : expr) x, P e0 → ∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Case e0 x e1 e2))
    → (∀ e1 : expr, P e1 → ∀ e2 : expr, P e2 → P (Pair e1 e2))
    → (∀ e : expr, P e → P (Fst e))
    → (∀ e : expr, P e → P (Snd e))
    → (∀ e : expr, P e → P (InjL e))
    → (∀ e : expr, P e → P (InjR e))
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
    → (∀ K e1 e2 i x, P (Cont i K) → P e1 → P e2 → P (Cont i (CaseCtx x e1 e2 :: K)))
    → (∀ K op e2 i, P (Cont i K) → P e2 → P (Cont i (BinOpLCtx op e2 :: K)))
    → (∀ K op v1 i, P (Cont i K) → Q v1 → P (Cont i (BinOpRCtx op v1 :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (FstCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (SndCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (InjLCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (InjRCtx :: K)))
    → (∀ K e1 e2 i, P (Cont i K) → P e1 → P e2 → P (Cont i (IfCtx e1 e2 :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (HallocCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (SallocCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (LoadCtx :: K)))
    → (∀ K i, P (Cont i K) → P (Cont i (MaskCtx :: K)))
    → (∀ K e2 i, P (Cont i K) → P e2 → P (Cont i (StoreLCtx e2 :: K)))
    → (∀ K v1 i, P (Cont i K) → Q v1 → P (Cont i (StoreRCtx v1 :: K)))
    → (∀ K e2 i, P (Cont i K) → P e2 → P (Cont i (ReturnLCtx e2 :: K)))
    → (∀ K v1 i, P (Cont i K) → Q v1 → P (Cont i (ReturnRCtx v1 :: K)))
    → (∀ e δ k f x, P e → Q (RecV δ k f x e))
    → (Q UnitV)
    → (∀ b, Q (NatV b))
    → (∀ b, Q (BoolV b))
    → (∀ v1 v2, Q v1 → Q v2 → Q (PairV v1 v2))
    -> (∀ v1, Q v1 -> Q (InjLV v1))
    -> (∀ v1, Q v1 -> Q (InjRV v1))
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
    → (∀ K i, Q (ContV i K) → Q (ContV i (InjLCtx :: K)))
    → (∀ K i, Q (ContV i K) → Q (ContV i (InjRCtx :: K)))
    → (∀ K e1 e2 i, Q (ContV i K) → P e1 → P e2 → Q (ContV i (IfCtx e1 e2 :: K)))
    → (∀ K e1 e2 i x, Q (ContV i K) → P e1 → P e2 → Q (ContV i (CaseCtx x e1 e2 :: K)))
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
    intros Hvar HRec HLetIn Happ Hunit Hnat Hbool Hbinop Hif Hcase Hpair Hfst Hsnd
      Hinjl Hinjr Hloc Hhalloc Hsalloc Hmask Hload
      Hstore
      HKnil HAppLCtx HAppRCtx HLetInCtx HPairLCtx HPairRCtx HCaseCtx
      HBinOpLCtx HBinOpRCtx HFstCtx HSndCtx HInjLCtx HInjRCtx HIfCtx
      HHallocCtx HSallocCtx HLoadCtx HMaskCtx HStoreLCtx HStoreRCtx
      HThrowLCtx HThrowRCtx
      HRecV HUnitV HNatV HBoolV HPairV HInjLV HInjRV HLocV
      HContV
      HKnilV HAppLCtxV HAppRCtxV HLetInCtxV
      HPairLCtxV HPairRCtxV HBinOpLCtxV
      HBinOpRCtxV HFstCtxV HSndCtxV HInjLCtxV HInjRCtxV HIfCtxV HCaseCtxV
      HHallocCtxV HSallocCtxV HLoadCtxV HMaskCtxV HStoreLCtxV HStoreRCtxV
      HThrowLCtxV HThrowRCtxV
      Hthrow e.
    refine (
        (fix fx (e : expr) {struct e} :=
           match e as u return (* F u → *) P u with
           | Var x => Hvar _
           | Rec δ k f x e => HRec _ δ k f x (fx e)
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
           | Case e0 x e1 e2 => Hcase _ _ (fx e0) _ (fx e1) _ (fx e2)
           | InjL e => Hinjl _ (fx e)
           | InjR e => Hinjr _ (fx e)
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
                      | RecV δ k f x e => HRecV _ _ _ _ _ (fx e)
                      | UnitV => HUnitV
                      | NatV n => HNatV n
                      | BoolV b => HBoolV b
                      | PairV v1 v2 => HPairV _ _ (hx v1) (hx v2)
                      | InjLV v1 => HInjLV _ (hx v1)
                      | InjRV v1 => HInjRV _ (hx v1)
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
                             | (InjLCtx) :: K' => HInjLCtxV _ _ (gx' K')
                             | (InjRCtx) :: K' => HInjRCtxV _ _ (gx' K')
                             | (IfCtx e1 e2) :: K' => HIfCtxV _ _ _ _ (gx' K') (fx e1) (fx e2)
                             | (CaseCtx x e1 e2) :: K' => HCaseCtxV _ _ _ _ _ (gx' K') (fx e1) (fx e2)
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
                  | (InjLCtx) :: K' => HInjLCtx _ _ (gx K')
                  | (InjRCtx) :: K' => HInjRCtx _ _ (gx K')
                  | (IfCtx e1 e2) :: K' => HIfCtx _ _ _ _ (gx K') (fx e1) (fx e2)
                  | (CaseCtx x e1 e2) :: K' => HCaseCtx _ _ _ _ _ (gx K') (fx e1) (fx e2)
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
           | |- Decision (?A ?B1 ?B2 ?B3 ?B4 ?B5 = ?A ?C1 ?C2 ?C3 ?C4 ?C5) =>
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               destruct (decide (B3 = C3)); [| right; inversion 1; tauto];
               destruct (decide (B4 = C4)); [| right; inversion 1; tauto];
               destruct (decide (B5 = C5)); [| right; inversion 1; tauto];
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
           | |- Decision (Cont ?i (?A ?B1 ?B2 ?B3 :: ?K1) = Cont ?i0 (?A ?C1 ?C2 ?C3 :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (Cont i K1 = Cont i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto];
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               destruct (decide (B3 = C3)); [| right; inversion 1; tauto];
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
           | |- Decision (ContV ?i (?A ?B1 ?B2 ?B3 :: ?K1) = ContV ?i0 (?A ?C1 ?C2 ?C3 :: ?K2)) =>
               let Hf := fresh "H" in
               destruct (decide (ContV i K1 = ContV i0 K2)) as [Hf|];
               [inversion Hf| right; inversion 1; subst; tauto];
               destruct (decide (B1 = C1)); [| right; inversion 1; tauto];
               destruct (decide (B2 = C2)); [| right; inversion 1; tauto];
               destruct (decide (B3 = C3)); [| right; inversion 1; tauto];
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


  Fixpoint shift_val (v : val) (off : Z) : option val :=
    match v with
    | RecV (local i) k f x e =>
        let j := (Z.of_nat i + off)%Z in
        if (j <? 0)%Z then None
        else 
          Some (RecV (local (Z.abs_nat j)) k f x e) (* e is only shifted once λe is invoked *)
    | LocV (local i) l =>
        let j := (Z.of_nat i + off)%Z in
        if (j <? 0)%Z then None
        else 
          Some (LocV (local (Z.abs_nat j)) l)
    | ContV i K =>
        let j := (Z.of_nat i + off)%Z in
        if (j <? 0)%Z then None
        else 
          Some (ContV (Z.abs_nat j) K) (* no need to shift K, since invoking it pops the stack to correct shape *)
    | PairV v1 v2 =>
        v1' ← shift_val v1 off;
        v2' ← shift_val v2 off;
        Some (PairV v1' v2')
    | InjLV v =>
        v' ← shift_val v off;
        Some (InjLV v')
    | InjRV v =>
        v' ← shift_val v off;
        Some (InjRV v')
    | _ => Some v
    end.

  Fixpoint shift_expr (e : expr) (off : Z) : option expr :=
    match e with
    | Var x => Some (Var x)
    | Rec (local i) k f x e => let j := (Z.of_nat i + off)%Z in
        if (j <? 0)%Z then None
        else 
          Some (Rec (local (Z.abs_nat j)) k f x e)
    | Rec δ k f x e => Some (Rec δ k f x e)
    | LetIn x e1 e2 =>
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (LetIn x e1' e2')
    | Call e1 e2 =>
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (Call e1' e2')
    | Unit => Some Unit
    | Nat n => Some (Nat n)
    | Bool b => Some (Bool b)
    | BinOp op e1 e2 =>
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (BinOp op e1' e2')
    | If e0 e1 e2 =>
        e0' ← shift_expr e0 off;
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (If e0' e1' e2')
    | Case e0 x e1 e2 =>
        e0' ← shift_expr e0 off;
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (Case e0' x e1' e2')
    | Pair e1 e2 =>
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (Pair e1' e2')
    | Fst e => e1' ← shift_expr e off; Some (Fst e1')
    | Snd e => e1' ← shift_expr e off; Some (Snd e1')
    | InjL e => e1' ← shift_expr e off; Some (InjL e1')
    | InjR e => e1' ← shift_expr e off; Some (InjR e1')
    | Loc (local i) l =>
        let j := (Z.of_nat i + off)%Z in
        if (j <? 0)%Z then None
        else 
          Some (Loc (local (Z.abs_nat j)) l)
    | Loc δ l => Some (Loc δ l)
    | Halloc e => e' ← shift_expr e off; Some (Halloc e')
    | Salloc e => e' ← shift_expr e off; Some (Salloc e')
    | Mask e => e' ← shift_expr e off; Some (Mask e')
    | Load e => e' ← shift_expr e off; Some (Load e')
    | Store e1 e2 =>
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (Store e1' e2')
    | Return e1 e2 =>
        e1' ← shift_expr e1 off;
        e2' ← shift_expr e2 off;
        Some (Return e1' e2')
    | Cont i K =>
        let j := (Z.of_nat i + off)%Z in
        if (j <? 0)%Z then None
        else 
          Some (Cont (Z.abs_nat j) K)
    end.

  Lemma shift_of_val v off :
    (shift_val v off) ≫= (λ v, Some (of_val v)) = shift_expr (of_val v) off.
  Proof.
    induction v;auto.
    - destruct δ =>// /=;case_match =>//.
    - destruct δ =>// /=;case_match =>//.
    - simpl. case_match =>//.
    - rewrite /=. destruct (shift_val v1 off),(shift_val v2 off); simpl in * =>//.
      all: destruct (shift_expr (of_val v1) off),(shift_expr (of_val v2) off); simpl in *;simplify_eq =>//.
    - rewrite /=. destruct (shift_val v off); simpl in * =>//.
      all: destruct (shift_expr (of_val v) off); simpl in *;simplify_eq =>//.
    - rewrite /=. destruct (shift_val v off); simpl in * =>//.
      all: destruct (shift_expr (of_val v) off); simpl in *;simplify_eq =>//.
  Qed.

  Definition heap : Type := gmap loc val.
  Definition stack : Type := list (gmap loc val).
  Definition state : Type := heap * stack.
  Definition observation : Type := Empty_set.

  Definition heap_of (σ : state) : heap := fst σ.
  Definition stack_of (σ : state) : stack := snd σ.
  Definition stack_expr : Type := nat * expr.
  Definition stack_val : Type := nat * val.
  
  (* Inductive scope_tag : tag -> Prop := *)
  (* | borrowScope : scope_tag borrow *)
  (* | globalScope : scope_tag global *)
  (* | localScope i : (i <= 0)%Z -> scope_tag (local i). *)

  Inductive permanent : val -> Prop :=
  | lamPerm k f x e : permanent (RecV global k f x e)
  | natPerm n : permanent (NatV n)
  | boolPerm b : permanent (BoolV b)
  | unitPerm : permanent UnitV
  | locPerm l : permanent (LocV global l)
  | injLPerm v : permanent v -> permanent (InjLV v)
  | injRPerm v : permanent v -> permanent (InjRV v)
  | pairPerm v1 v2 : permanent v1 -> permanent v2 -> permanent (PairV v1 v2).

  (* Inductive scope : val -> Z -> Prop := *)
  (* | permScope v n : permanent v -> scope v n *)
  (* | locScope δ l n : scope_tag δ -> scope (LocV δ l) n *)
  (* | lamScope δ k x e n : scope_tag δ -> scope (LamV δ k x e) n *)
  (* | contScope i K j : (i <= j)%Z -> scope (ContV i K) j. *)

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

  Inductive head_step : list ectx_item -> stack_expr -> state -> list observation -> stack_expr -> state -> list stack_expr -> RedMode -> Prop :=
  (** Local Lam-β *)
  | LamBetaLocalS n K k f x e1 (i : nat) e2 v2 σ e1' v2' :
    to_val e2 = Some v2 ->
    shift_val v2 1 = Some v2' ->
    shift_expr e1 (i + 1)%Z = Some e1' ->
    head_step K (n,Call (Rec (local i) k f x e1) e2) σ []
      (n+1,Return (Cont 1 K) (subst' k (ContV 1 K) (subst' f (RecV (local i) k f x e1) (subst' x v2' e1')))) (push σ) [] CaptureMode

  (** Global Lam-β *)
  | LamBetaGlobalS n K k f x e1 e2 v2 σ v2' :
    to_val e2 = Some v2 ->
    shift_val v2 1 = Some v2' ->
    head_step K (n, Call (Rec global k f x e1) e2) σ []
      (n+1,Return (Cont 1 K) (subst' k (ContV 1 K) (subst' f (RecV global k f x e1) (subst' x v2' e1)))) (push σ) [] CaptureMode

  (** Return *)
  | ReturnS n K K' (i : nat) e e' v σ :
    to_val e = Some v ->
    shift_expr e (-i) = Some e' ->
    i ≤ length (stack_of σ) ->
    head_step K (n, Return (Cont i K') e) σ [] (n - i, foldl (flip fill_item) e' K') (popN σ i) [] ThrowMode

  (** zeta *)
  | ZetaS n K x e1 e2 v1 σ :
    to_val e1 = Some v1 ->
    head_step K (n, LetIn x e1 e2) σ [] (n, subst' x v1 e2) σ [] NormalMode

  (** Products *)
  | FstS n K e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step K (n, Fst (Pair e1 e2)) σ [] (n,e1) σ [] NormalMode
  | SndS n K e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    head_step K (n,Snd (Pair e1 e2)) σ [] (n,e2) σ [] NormalMode

  (** Sums *)
  | CaseInjL n K v x e1 e2 σ :
    head_step K (n, Case (InjL (of_val v)) x e1 e2) σ [] (n, subst' x v e1) σ [] NormalMode
  | CaseInjR n K v x e1 e2 σ :
    head_step K (n, Case (InjR (of_val v)) x e1 e2) σ [] (n, subst' x v e2) σ [] NormalMode

  (** BinOp *)
  | BinOpS n K op e1 e2 v1 v2 w σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    binop_eval op v1 v2 = Some w →
    head_step K (n, BinOp op e1 e2) σ [] (n, of_val w) σ [] NormalMode

  (** Allocation *)
  | HallocS n K e v σ l :
    to_val e = Some v ->
    permanent v ->
    [[σ @@]] !! l = None ->
    head_step K (n, Halloc e) σ [] (n, Loc global l) (<[l@@:=v]>σ) [] NormalMode

  | SallocS n K e v σ l :
    to_val e = Some v ->
    [[σ @ 0]] !! l = None ->
    head_step K (n, Salloc e) σ [] (n, Loc (local 0) l) (<[0@l:=v]>σ) [] NormalMode

  (** Loading *)
  | LoadHeapS n K v l δ σ :
    [[σ @@]] !! l = Some v ->
    heap_tag δ ->
    head_step K (n, Load (Loc δ l)) σ [] (n, of_val v) σ [] NormalMode

  | LoadStackS n K v v' l (i : nat) σ :
    [[σ @ (Z.abs_nat i)]] !! l = Some v ->
    shift_val v i = Some v' ->
    head_step K (n, Load (Loc (local i) l)) σ [] (n, of_val v') σ [] NormalMode

  (** Storing *)
  | StoreHeapS n K e v l δ σ :
    to_val e = Some v ->
    permanent v ->
    heap_tag δ ->
    is_Some ([[σ @@]] !! l) ->
    head_step K (n, Store (Loc δ l) e) σ [] (n,Unit) (<[l@@:=v]>σ) [] NormalMode

  | StoreStackS n K e v v' l (i : nat) σ :
    to_val e = Some v ->
    shift_val v (- i) = Some v' ->
    is_Some ([[σ @ i]] !! l) ->
    head_step K (n, Store (Loc (local i) l) e) σ [] (n,Unit) (<[i@l:=v']>σ) [] NormalMode

  (** Downgrade Heap Location *)
  | MaskS K l σ n :
    head_step K (n, Mask (Loc global l)) σ [] (n, Loc borrow l) σ [] NormalMode

  (** If then else *)
  | IfFalse n K e1 e2 σ :
    head_step K (n, If (#♭ false) e1 e2) σ [] (n, e2) σ [] NormalMode
  | IfTrue n K e1 e2 σ :
    head_step K (n, If (#♭ true) e1 e2) σ [] (n,e1) σ [] NormalMode

  .

  Definition stack_fill_item Ki (e : stack_expr) :=
    (e.1,fill_item Ki e.2).
  Definition stack_to_val (e : stack_expr) :=
    to_val e.2 ≫= λ v, Some (e.1,v).
  Definition stack_of_val (v : stack_val) :=
    (v.1,of_val v.2).
  Lemma stack_to_of_val v : stack_to_val (stack_of_val v) = Some v.
  Proof. rewrite /stack_to_val /stack_of_val /= to_of_val /=. destruct v;auto. Qed.
  Lemma stack_of_to_val e v : stack_to_val e = Some v -> stack_of_val v = e.
  Proof. rewrite /stack_to_val /stack_of_val /=. destruct (to_val e.2) eqn:Hsome => /= //.
         destruct e;simpl in *. intros HH. inversion HH. simpl.
         apply of_to_val in Hsome as ->. auto. Qed.

  Lemma fill_item_val Ki e :
    is_Some (stack_to_val (stack_fill_item Ki e)) → is_Some (stack_to_val e).
  Proof. intros [v ?]. unfold stack_to_val. unfold stack_to_val in H.
         destruct Ki; simplify_option_eq; simpl; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (stack_fill_item Ki).
  Proof. intros ? ?.  destruct x,y;simpl.
         destruct Ki; intros ?; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck K e1 σ1 κ e2 σ2 ef rm :
    head_step K e1 σ1 κ e2 σ2 ef rm → stack_to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val K Ki e σ1 κ e2 σ2 ef rm :
    head_step K (stack_fill_item Ki e) σ1 κ e2 σ2 ef rm → is_Some (stack_to_val e).
  Proof. destruct e. destruct Ki; inversion_clear 1; simplify_option_eq; eauto.
         all: try (rewrite /stack_to_val /= H0 /= //).
         all: try (rewrite /stack_to_val /= H1 /= //).
         all: rewrite /stack_to_val /= to_of_val /= //.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    stack_to_val e1 = None → stack_to_val e2 = None →
    stack_fill_item Ki1 e1 = stack_fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct e1,e2. rewrite /stack_to_val /=. destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
      repeat match goal with
        | H : (to_val (of_val _)) ≫= _ = None |- _ => by rewrite to_of_val in H
        end; auto.
  Qed.

  Lemma red_mode_det K e1 σ1 κ e2 σ2 efs rm :
    head_step K e1 σ1 κ e2 σ2 efs rm →
    ∀ K' σ1' κ' e2' σ2' efs' rm',
      head_step K' e1 σ1' κ' e2' σ2' efs' rm' → rm' = rm.
  Proof. by destruct 1; intros ??????; inversion 1. Qed.           

  Definition capture K (e : stack_expr) :=
    match e.2 with
    | Call (Rec global k f x e1) e2 =>
        v2 ← to_val e2; v2' ← shift_val v2 1;
        Some (e.1+1,Return (Cont (1) K) (subst' k (ContV (1) K) (subst' f (RecV global k f x e1) (subst' x v2' e1))))
    | Call (Rec (local i) k f x e1) e2 =>
        v2 ← to_val e2; v2' ← shift_val v2 1; e1' ← shift_expr e1 (i + 1);
        Some (e.1+1,Return (Cont (1) K) (subst' k (ContV (1) K) (subst' f (RecV (local i) k f x e1) (subst' x v2' e1'))))
    | _ => None
    end.

  Lemma ectxi_capture_captures K e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs CaptureMode →
    capture K e1 = Some e2.
  Proof.
    inversion 1; eauto.
    - simplify_eq. unfold capture. simpl.
      simplify_option_eq =>//.
    - unfold capture. simplify_eq. simpl. simplify_option_eq. auto.
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
    - unfold capture. simplify_option_eq.
      eauto using head_step.
    - unfold capture. simplify_option_eq. eauto using head_step.
  Qed.

  Lemma ectxi_throw_reduciblity K K' e1 σ1 κ e2 σ2 efs :
    head_step K e1 σ1 κ e2 σ2 efs ThrowMode →
    head_step K' e1 σ1 κ e2 σ2 efs ThrowMode.
  Proof. inversion 1; econstructor; eauto. Qed.

  
  Lemma halloc_fresh n K e v σ :
    let l := fresh (dom (heap_of σ)) in
    to_val e = Some v →
    permanent v ->
    head_step K (n,Halloc e) σ [] (n,Loc global l) (<[l@@:=v]>σ) [] NormalMode.
  Proof. intros; apply HallocS;auto. apply not_elem_of_dom,is_fresh. Qed.

  Lemma salloc_fresh n K e v σ s :
    let l := fresh (dom s) in
    stack_of σ !! (length (stack_of σ) - 1) = Some s ->
    to_val e = Some v →
    head_step K (n,Salloc e) σ [] (n, Loc (local 0) l) (<[0 @ l:=v]>σ) [] NormalMode.
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
    (lang.stack_expr) lang.stack_val lang.ectx_item lang.state lang.observation :=
  {|
    of_val := lang.stack_of_val;
    to_val := lang.stack_to_val;
    fill_item := lang.stack_fill_item;
    head_step := lang.head_step;
    capture := lang.capture
  |}.
Solve Obligations with simpl; eauto using lang.stack_to_of_val, lang.stack_of_to_val,
  lang.val_stuck, lang.fill_item_val, lang.fill_item_no_val_inj,
  lang.head_ctx_step_val, lang.red_mode_det, lang.ectxi_capture_captures,
  lang.ectxi_normal_reduciblity, lang.ectxi_throw_reduciblity,
  lang.ectxi_capture_reduciblity.

Canonical Structure lang := CC_ectx_lang (lang.stack_expr).

Export lang.

Inductive throw_reducible_fill : expr -> nat -> Prop :=
| throw_reduce_fill i K v Ks : throw_reducible_fill (foldl (flip fill_item) (Return (Cont i K) (of_val v)) Ks) i.
(* | throw_reduce_fill_ctx n Ks e : throw_reducible_fill (n, foldl (flip fill_item) Ks e). *)

Inductive throw_reducible : expr -> Prop :=
| throw_reduce i K v : throw_reducible ( Return (Cont i K) (of_val v))
| throw_reduce_ctx K e : throw_reducible (e) -> throw_reducible ( fill_item K e).

Inductive throw_reducible_i : expr -> nat -> Prop :=
| throw_reduce_i i K v : throw_reducible_i (Return (Cont i K) (of_val v)) i
| throw_reduce_i_ctx K e i : throw_reducible_i e i -> throw_reducible_i (fill_item K e) i.

Local Ltac simpl_throw_red_solve IH ptrn K := destruct IH;                                           
    [left; rewrite /= -/(fill_item ptrn _); constructor; auto|
      right; intros Hcontr; inversion Hcontr as [|? ? ? HH]; simplify_eq; try (by destruct K; inversion HH; simpl in *; simplify_eq)].

Lemma throw_reducible_fill_iff e i :
  throw_reducible_fill e i <-> throw_reducible_i e i.
Proof.
  split; intros He.
  - induction He; try constructor.
    induction Ks using rev_ind.
    + simpl. constructor.
    + rewrite foldl_snoc /=. constructor. auto.
  - induction He.
    + assert (Return (Cont i K) (of_val v) = foldl (flip fill_item) (Return (Cont i K) (of_val v)) []) as ->;auto. constructor.
    + inversion IHHe;subst. eassert (fill_item _ _ = flip fill_item _ _) as ->;[eauto|].
      rewrite -(foldl_snoc (flip fill_item)). constructor.
Qed.


Definition is_cont (e1 : expr) :=
  match e1 with
  | Cont i K => true
  | _ => false
  end.

Definition throw_reducible_dec e : Decision (throw_reducible e).
Proof.
  induction e; try (right;intros Hcontr;inversion Hcontr;by destruct K).
  - simpl_throw_red_solve IHe1 (LetInCtx x e2) K. 
  - destruct IHe1.
    + left. rewrite -/(fill_item (BinOpLCtx _ _) _). constructor;auto.
    + destruct (to_val e1) eqn:Hv.
      * destruct IHe2.
        { rewrite -(of_to_val e1 v)//. left. rewrite -/(fill_item (BinOpRCtx _ _) _). constructor;auto. }
        { right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq;done. }
      * right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; try done.
        by rewrite to_of_val in Hv.
  - simpl_throw_red_solve IHe HallocCtx K.
  - simpl_throw_red_solve IHe SallocCtx K.
  - simpl_throw_red_solve IHe LoadCtx K.
  - destruct IHe1.
    + left. rewrite -/(fill_item (StoreLCtx _) _). constructor;auto.
    + destruct (to_val e1) eqn:Hv.
      * destruct IHe2.
        { rewrite -(of_to_val e1 v)//. left. rewrite -/(fill_item (StoreRCtx _) _). constructor;auto. }
        { right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; done. }
      * right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; try done.
        by rewrite to_of_val in Hv.
  - simpl_throw_red_solve IHe MaskCtx K.
  - right;intros Hcontr;inversion Hcontr;by destruct K0.
  - destruct IHe1.
    + left. rewrite -/(fill_item (CallLCtx _) _). constructor;auto.
    + destruct (to_val e1) eqn:Hv.
      * destruct IHe2.
        { rewrite -(of_to_val e1 v)//. left. rewrite -/(fill_item (CallRCtx _) _). constructor;auto. }
        { right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; done. }
      * right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; try done.
        by rewrite to_of_val in Hv.
  - destruct (is_cont (e1)) eqn:Hcont.
    + destruct e1;inversion Hcont. destruct (to_val e2) eqn:Hv.
      * rewrite -(of_to_val e2 v)//;left;constructor.
      * destruct IHe2.
        { left. rewrite -(of_to_val (Cont i K) (ContV i K))// -/(fill_item (ReturnRCtx _) _).
          constructor;auto. }
        right. intros Hcontr; inversion Hcontr; simpl in *; simplify_eq;[rewrite to_of_val in Hv;done|].
        destruct K0;inversion H;simpl in *; simplify_eq;[inversion H0; destruct K0; done|congruence].
    + destruct IHe2.
      * destruct (to_val e1) eqn:Hv.
        { rewrite -(of_to_val e1 v)//  -/(fill_item (ReturnRCtx v) _). left. constructor; auto. }
        simpl_throw_red_solve IHe1 (ReturnLCtx e2) K; simpl in *;simplify_eq.
        destruct K;inversion HH;simpl in *; simplify_eq;[done|]. 
        rewrite to_of_val in Hv. done.
      * simpl_throw_red_solve IHe1 (ReturnLCtx e2) K; simplify_eq.
  - destruct IHe1.
    + left. rewrite -/(fill_item (PairLCtx _) _). constructor;auto.
    + destruct (to_val e1) eqn:Hv.
      * destruct IHe2.
        { rewrite -(of_to_val e1 v)//. left. rewrite -/(fill_item (PairRCtx _) _). constructor;auto. }
        { right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; done. }
      * right. intros Hcontr; inversion Hcontr; destruct K; inversion H; simpl in *; simplify_eq; try done.
        by rewrite to_of_val in Hv.
  - simpl_throw_red_solve IHe FstCtx K.
  - simpl_throw_red_solve IHe SndCtx K.
  - simpl_throw_red_solve IHe InjLCtx K.
  - simpl_throw_red_solve IHe InjRCtx K.
  - simpl_throw_red_solve IHe1 (CaseCtx x e2 e3) K.
  - simpl_throw_red_solve IHe1 (IfCtx e2 e3) K.
Qed.

Lemma throw_reducible_exists_i (e : expr) :
  throw_reducible e <->
  exists i, throw_reducible_i e i.
Proof.
  split.
  - intros H. induction H.
    + exists i. constructor.
    + destruct IHthrow_reducible as [i Hi].
      exists i. constructor. auto.
  - intros H. destruct H as [i Hi]. induction Hi.
    + constructor.
    + constructor. auto.
Qed.

Fixpoint construct_ctx (e : expr) : (ectx * expr) :=
  match e with
  | Var _ | Rec _ _ _ _ _ | Nat _ | Bool _ | Loc _ _ | Cont _ _ | Unit => ([],e)
  | LetIn x e1 e2 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [LetInCtx x e2],e')
  | BinOp op e1 e2 => match to_val e1 with
                     | Some v => let '(Ks,e') := construct_ctx e2 in (Ks ++ [BinOpRCtx op v],e')
                     | None => let '(Ks,e') := construct_ctx e1 in (Ks ++ [BinOpLCtx op e2],e')
                     end
  | Halloc e1 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [HallocCtx],e')
  | Salloc e1 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [SallocCtx],e')
  | Load e1 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [LoadCtx],e')
  | Store e1 e2 => match to_val e1 with
                  | Some v => let '(Ks,e') := construct_ctx e2 in (Ks ++ [StoreRCtx v],e')
                  | None => let '(Ks,e') := construct_ctx e1 in (Ks ++ [StoreLCtx e2],e')
                  end
  | Mask e1 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [MaskCtx],e')
  | Call e1 e2 => match to_val e1 with
                 | Some v => let '(Ks,e') := construct_ctx e2 in (Ks ++ [CallRCtx v],e')
                 | None => let '(Ks,e') := construct_ctx e1 in (Ks ++ [CallLCtx e2],e')
                 end
  | Return e1 e2 => match to_val e1 with
                   | Some v => let '(Ks,e') := construct_ctx e2 in (Ks ++ [ReturnRCtx v],e')
                   | None => let '(Ks,e') := construct_ctx e1 in (Ks ++ [ReturnLCtx e2],e')
                   end
  | Pair e1 e2 => match to_val e1,to_val e2 with
                 | Some v1, Some v2 => ([],e)
                 | Some v, None => let '(Ks,e') := construct_ctx e2 in (Ks ++ [PairRCtx v],e')
                 | None,_ => let '(Ks,e') := construct_ctx e1 in (Ks ++ [PairLCtx e2],e')
                 end
  | Fst e1 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [FstCtx],e')
  | Snd e1 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [SndCtx],e')
  | If e1 e2 e3 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [IfCtx e2 e3],e')
  | InjL e1 => match to_val e1 with
              | Some v1 => ([],e)
              | None => let '(Ks,e') := construct_ctx e1 in (Ks ++ [InjLCtx],e')
              end
  | InjR e1 => match to_val e1 with
              | Some v1 => ([],e)
              | None => let '(Ks,e') := construct_ctx e1 in (Ks ++ [InjRCtx],e')
              end
  | Case e1 x e2 e3 => let '(Ks,e') := construct_ctx e1 in (Ks ++ [CaseCtx x e2 e3],e')
  end.

Definition stack_construct_ctx (e : stack_expr) : (ectx * stack_expr) :=
  let '(Ks,e') := construct_ctx e.2 in (Ks,(e.1,e')).

Lemma snoc_eq {A : Type} (l1 l2 : list A) (a1 a2 : A) :
  l1 ++ [a1] = l2 ++ [a2] -> l1 = l2 /\ a1 = a2.
Proof.
  intros Heq.
  apply app_inj_2 in Heq as [Heq1 Heq2];auto.
  simplify_eq. auto.
Qed.

Lemma construct_ctx_fill e Ks e' :
  construct_ctx e = (Ks,e') -> e = foldl (flip fill_item) e' Ks.
Proof.
  revert e e'. induction Ks using rev_ind;intros e e'.
  - simpl. intros Heq.
    destruct e;simpl in *;inversion Heq;auto.
    all: try (case_match;inversion Heq; by apply app_nil in H2 as [? ?]).
    all: try (case_match;case_match;inversion Heq; by apply app_nil in H3 as [? ?]).
    case_match;[case_match|];inversion Heq;auto.
    3,4: case_match;inversion Heq;auto.
    all: case_match;inversion Heq;destruct l;simpl in *;done.    
  - destruct e; simpl;intros Heq;inversion Heq;simpl;auto.
    all: rewrite foldl_snoc.
    all:try (case_match;inversion Heq;subst;apply snoc_eq in H2 as [? ?];simplify_eq).
    all:try by (rewrite -(IHKs e1)//).
    all:try (case_match;case_match;inversion Heq;apply snoc_eq in H3 as [? ?];simplify_eq).
    all:try (rewrite -(IHKs e2) // /= (of_to_val e1) //).
    all:try by (rewrite -(IHKs e1) /= //).
    all:try by (rewrite -(IHKs e) /= //).
    all: case_match;try case_match;simplify_eq;destruct Ks => //.
    all: try case_match;simplify_eq. all: apply snoc_eq in H0 as [? ?];simplify_eq.
    all: try by (rewrite -(IHKs e2)// /= (of_to_val e1)//).
    all: try rewrite -(IHKs e1)//.
    all: rewrite -(IHKs e)//.
Qed.

Definition find_i (e : expr) : option nat :=
  let '(Ks,e') := construct_ctx e in
  match (Ks,e') with
  | (ReturnRCtx (ContV i _) :: Ks', e) => to_val e ≫= λ _, Some i
  | (_,_) => None
  end.

Compute construct_ctx (Fst (Return (Cont 0 [FstCtx]) (Nat 0))).
Compute (fill [ReturnRCtx (ContV 0 [FstCtx]); FstCtx] (0,Nat 0)).
Compute (find_i (Fst (Return (Cont 0 [FstCtx]) (Nat 0)))).

Lemma construct_ctx_val e e' :
  construct_ctx e = ([], e') ->
  ((is_Some (to_val e) \/ (exists b, e = Var b)) /\ e = e').
Proof.
  intros Hctx.
  destruct e;inversion Hctx;subst;simpl.
  all: try by (split;eauto).
  all: try (case_match;destruct l;done).
  all: try (case_match;case_match;destruct l;done).
  case_match;case_match;simpl;simplify_eq;eauto.
  3,4: case_match;simpl;simplify_eq;eauto.
  1,3,4: case_match;destruct l;done.
  destruct l;done.
Qed.

Lemma find_i_throw_reducible e i :
  find_i e = Some i -> throw_reducible_i e i.
Proof.
  intros Hi. unfold find_i in Hi.
  destruct (construct_ctx e) as [Ks e'] eqn:He.
  destruct Ks;[done|].
  destruct e0;try done. destruct v1;try done.
  destruct (to_val e') eqn:He';try done. simpl in Hi. simplify_eq.
  apply throw_reducible_fill_iff.
  apply construct_ctx_fill in He as Heq. subst e.
  simpl. rewrite -(of_to_val e' v)//.
Qed.
  
Lemma construct_ctx_to_val e v :
  to_val e = Some v ->
  construct_ctx e = ([],e).
Proof.
  intros Hv.
  induction e;inversion Hv;simpl in *;auto.
  case_match;simpl in *.
  case_match;simpl in *;auto.
  done. done.
  all: case_match;simpl in *; auto;done.
Qed.

Lemma construct_ctx_of_val e :
  construct_ctx (of_val e) = ([],of_val e).
Proof.
  destruct e;simpl;auto.
  all: rewrite !to_of_val //.
Qed.

Lemma to_val_foldl_None e Ks :
  to_val e = None ->
  to_val (foldl (flip fill_item) e Ks) = None.
Proof.
  intros Hnone.
  induction Ks using rev_ind;simpl;auto.
  rewrite foldl_snoc;simpl.
  destruct x;simpl;auto.
  all: rewrite IHKs//.
  rewrite to_of_val /=//.
Qed.
  
Lemma find_i_fill_item e i K:
  find_i e = Some i ->
  find_i (fill_item K e) = Some i.
Proof.
  rewrite /find_i /=. case_match.
  case_match;[done|]. destruct e1;try done.
  destruct v1;try done.
  intros Hval. destruct (to_val e0) eqn:Hv;simpl in *;[|done].
  simplify_eq. apply construct_ctx_fill in H as Heq; subst e.
  simpl. clear H. revert K. induction l0 using rev_ind;intros K.
  - simpl. destruct K;simpl; erewrite construct_ctx_to_val;eauto;rewrite /= //.
    all: try rewrite Hv /= //. all: try rewrite to_of_val /= // Hv //.
  - rewrite foldl_snoc. simpl.
    specialize (IHl0 x).
    case_match. destruct l;try done.
    destruct e1;try done. destruct v1;try done.
    destruct (to_val e) eqn:Hval;try done.
    simpl in *. simplify_eq.
    destruct K;simpl;try rewrite H /= Hval/=;auto.
    all: try rewrite to_of_val H /= Hval /= //.
    all: rewrite -/(flip fill_item _ x) -foldl_snoc.
    all: rewrite to_val_foldl_None//.
    all: try rewrite foldl_snoc /flip /= H /= Hval /= //.
    rewrite to_of_val.
    rewrite foldl_snoc /flip /= H /= Hval /= //.
Qed.

Lemma find_i_fill e i Ks :
  find_i e = Some i ->
  find_i (foldl (flip fill_item) e Ks) = Some i.
Proof.
  intros Hf.
  induction Ks using rev_ind.
  - simpl. auto.
  - rewrite foldl_snoc.
    apply find_i_fill_item =>//.
Qed.
    
Lemma throw_reducible_find_i e i :
  throw_reducible_i e i -> find_i e = Some i.
Proof.
  intros Hred.
  induction Hred;subst.
  - unfold find_i. simpl.
    erewrite construct_ctx_to_val;[|apply to_of_val].
    rewrite /= to_of_val /= //.
  -  apply find_i_fill_item. auto.
Qed.

Lemma throw_reducible_find_i_iff e i :
  throw_reducible_i e i <-> find_i e = Some i.
Proof.
  split.
  - apply throw_reducible_find_i.
  - apply find_i_throw_reducible.
Qed.

Lemma throw_reducible_of_val_false v1 i : throw_reducible_i (of_val v1) i -> False.
Proof.
  intros Ht.
  remember (of_val v1) as e in Ht.
  generalize dependent v1.
  induction Ht.
  - intros. destruct v1;done.
  - intros. destruct K,v1;simpl in Heqe;try done.
    all: inversion Heqe;subst; eapply IHHt;eauto.
Qed.    
  
Lemma fill_item_find_i e i K:
  to_val e = None ->
  find_i (fill_item K e) = Some i ->
  find_i e = Some i.
Proof.
  rewrite -!throw_reducible_find_i_iff.
  intros He Ht.
  remember (fill_item K e) as e' in Ht.
  generalize dependent K.
  generalize dependent e.
  induction Ht;intros e' He K' Heqe'.
  - subst. destruct K';inversion Heqe';subst.
    done. rewrite to_of_val in He. done.
  - destruct K,K';inversion Heqe';subst;auto.
    all: try by rewrite to_of_val in He.
    all: inversion Ht;subst;[destruct v1;done|].
    all: destruct K,v1;try done;inversion H;simplify_eq;
      exfalso;eapply throw_reducible_of_val_false;eauto.
Qed.

Lemma fill_find_i e i Ks :
  to_val e = None ->
  find_i (foldl (flip fill_item) e Ks) = Some i ->
  find_i e = Some i.
Proof.
  intros Hv Hf.
  induction Ks using rev_ind.
  - simpl. auto.
  - rewrite foldl_snoc in Hf.
    apply IHKs.
    apply fill_item_find_i with (K:=x);eauto.
    apply to_val_foldl_None =>//.    
Qed.

Lemma fill_proj (e : stack_expr) (K : ectx) :
  (foldl (flip stack_fill_item) e K).2 = foldl (flip fill_item) e.2 K.
Proof.
  destruct e;simpl. induction K using rev_ind;simpl;auto.
  rewrite !foldl_snoc.
  simpl. rewrite IHK. auto.
Qed.

Lemma fill_proj_fst_eq (e : stack_expr) (K : ectx) :
  (foldl (flip stack_fill_item) e K).1 = e.1.
Proof.
  destruct e;simpl. induction K using rev_ind;simpl;auto.
  rewrite !foldl_snoc.
  simpl. rewrite IHK. auto.
Qed.

Lemma fill_proj_eq (e : stack_expr) (K : ectx) :
  foldl (flip stack_fill_item) e K = (e.1,foldl (flip fill_item) e.2 K).
Proof.
  destruct e;simpl. induction K using rev_ind;simpl;auto.
  rewrite !foldl_snoc.
  simpl. rewrite IHK. auto.
Qed.

Definition is_atomic (e : stack_expr) : Prop :=
  match e.2 with
  | Halloc e => is_Some (to_val e)
  | Salloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
Lemma is_atomic_sub_values e : is_atomic e → sub_values e.
Proof.
  destruct e as [n e]; rewrite /is_atomic /=; destruct e; inversion 1; simpl; apply ectxi_language_sub_values;
    intros [] ?; inversion 1; subst; simpl in *.
  all: try rewrite /stack_to_val H0 /=;eauto.
  inversion H0;rewrite /stack_to_val H3 //.
  inversion H1;rewrite /stack_to_val H3 //.
Qed.
Lemma is_atomic_correct e : is_atomic e → Atomic StronglyAtomic e.
Proof.
  intros ?; apply ectx_language_atomic; simpl.
  - destruct 1; simpl; try done; rewrite /stack_to_val /= ?to_of_val; eauto.
  - apply ectxi_language_sub_values => Ki e' Heq; subst; simpl in *.
    destruct e';simpl in *.
    rewrite /stack_fill_item /= in H.
    rewrite /stack_to_val /=.
    destruct Ki; simpl in *; inversion H.
    all: try rewrite H0 /= //.
    inversion H0. rewrite H2 /= //.
    inversion H1. rewrite H2 /= //.
Qed.
Lemma is_atomic_normal e : is_atomic e → is_normal e.
Proof. destruct e;simpl. by destruct e; inversion 1; intros ????; inversion 1; simpl. Qed.

Lemma is_atomic_find_i_none :
  ∀ (e : stack_expr), is_atomic e → find_i e.2 = None.
Proof.
  intros e Hatomic.
  destruct (find_i e.2) eqn:Hsome =>//.
  exfalso. (* apply find_i_throw_reducible in Hsome. *)
  destruct e;simpl in *. destruct e;try done.
  4: destruct Hatomic as [ [v1 Hv] [v2 Hv2] ].
  1,2,3: destruct Hatomic as [v Hv].
  all: unfold find_i in Hsome; simpl in Hsome.
  all: apply construct_ctx_to_val in Hv as Hv'.
  4: apply construct_ctx_to_val in Hv2 as Hv2'.
  all: rewrite Hv' /= in Hsome; try done.
  by rewrite Hv Hv2' /= in Hsome.
Qed.
  

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
