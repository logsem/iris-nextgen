From nextgen.case_study.program_logic Require Import weakestpre CC_ectx_language.
From nextgen.case_study Require Export stack_lang.
From iris.prelude Require Export options.
From stdpp Require Export pretty strings binders.

Global Instance pretty_loc : Pretty loc := string_of_pos.

Global Instance pretty_binder : Pretty binder :=
  λ b, match b with
       | BNamed x => x
       | BAnon => "<>"
       end.

Global Instance pretty_tag : Pretty tag :=
  λ t, match t with
       | global => "global"
       | borrow => "borrow"
       | local i => "local " +:+ pretty i
       end.

(** Note that this instance does not print function bodies or continuation contexts and is thus not
injective (unlike most `pretty` instances). *)
Global Instance pretty_val : Pretty val :=
  fix go v :=
    match v with
    | ContV i K => "Cont " +:+ pretty i +:+ "[<ctx>]"
    | LocV δ l => "#v" +:+ "[" +:+ pretty δ +:+ ", " +:+ pretty l +:+ "]"
    | NatV n => "#v" +:+ pretty n
    | BoolV b => "#v" +:+ if b then "true" else "false"
    | UnitV => "#v()"
    | LamV δ k x e => "λ: " +:+ pretty δ +:+ ", " +:+ pretty k +:+ ", " +:+ pretty x +:+ ", <body>"
    | PairV v1 v2 => "<" +:+ go v1 +:+ ", " +:+ go v2 +:+ ">"
    end.

Global Instance pretty_bin_op : Pretty binop :=
  λ op, match op with
        | Sub => "-"
        | Le => "≤"
        | Lt => "<"
        | Eq => "="
        | _ => "+"
        end.

Definition LocT : Type := tag * loc.
Definition LocP (p: LocT) : expr := Loc p.1 p.2.

(** Coercions to make programs easier to type. *)
Coercion Nat : nat >-> expr.
Coercion Bool : bool >-> expr.
Coercion Var : string >-> expr.
Coercion Call : expr >-> Funclass.
Coercion LocP : LocT >-> expr.
(** Define some derived forms. *)
Notation Seq e1 e2 := (LetIn BAnon e1 e2) (only parsing).
Notation SeqCtx e2 := (LetInCtx BAnon e2) (only parsing).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# ( δ , l )" := (LocV δ l%Z%V%stdpp) (at level 8, format "# ( δ , l )").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "< e1 , e2 , .. , en >" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "< e1 , e2 , .. , en >" := (PairV .. (PairV e1 e2) .. en) : val_scope.

Notation "()" := lang.Unit : expr_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'href' e" := (Halloc e%E) (at level 10) : expr_scope.
Notation "'sref' e" := (Salloc e%E) (at level 10) : expr_scope.

Notation "e1 + e2" := (BinOp Add e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp Sub e1%E e2%E) : expr_scope.

Notation "e1 ≤ e2" := (BinOp Le e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp Lt e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (BinOp Eq e1%E e2%E) : expr_scope.

(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
                                             (at level 200, e1, e2, e3 at level 200) : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (Bool false)) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (Bool true) e2%E) (only parsing) : expr_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
(* | Lam (δ : tag) (k x : binder) (e : expr)*)
Notation "λ: δ , k , x , e" := (Lam δ k%binder x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  δ ,  k ,  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: δ , k , x y .. z , e" := (Lam δ k%binder x%binder (Lam δ k%binder y%binder .. (Lam δ k%binder z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
    format "'[' 'λ:'  δ ,  k ,  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "λ: δ , k , x , e" := (LamV δ k%binder x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  δ ,  k ,  x ,  '/  ' e ']'") : val_scope.
Notation "λ: δ , k , x y .. z , e" := (LamV δ k%binder x%binder (LamV δ k%binder y%binder .. (LamV δ k%binder z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  δ ,  k ,  x  y  ..  z ,  '/  ' e ']'") : val_scope.

Notation "'let:' x := e1 'in' e2" := (LetIn x%binder e1%E e2%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Seq e1%E e2%E)
  (at level 100, e2 at level 200,
    format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

(* Overloading the bi notation of Texan triples such that the postcondition is wrapped in a plainly *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' ? {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' ? {{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }}) : stdpp_scope.
