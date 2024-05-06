(** Overriding some of the WP notations to work over different types [A] *)

From stdpp Require Export coPset.
From iris.bi Require Export weakestpre bi.
From iris.bi Require Import interface derived_connectives.
From iris.prelude Require Import options.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; ↑ a ; E {{ Φ } }" := (wp (s,a) E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ ↑ a ; E {{ Φ } }" := (wp (NotStuck,a) E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ ↑ a ; E ? {{ Φ } }" := (wp (MaybeStuck,a) E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ ↑ a {{ Φ } }" := (wp (NotStuck,a) ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ ↑ a ? {{ Φ } }" := (wp (MaybeStuck,a) ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
(** The general approach we use for all these complex notations: an outer '[hv'
to switch bwteen "horizontal mode" where it all fits on one line, and "vertical
mode" where each '/' becomes a line break. Then, as appropriate, nested boxes
('['...']') for things like preconditions and postconditions such that they are
maximally horizontal and suitably indented inside the parentheses that surround
them. *)
Notation "'WP' e @ s ; ↑ a ; E {{ v , Q } }" := (wp (s,a) E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' ↑ a ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ ↑ a ; E {{ v , Q } }" := (wp (NotStuck,a) E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' ↑ a ;  '/' E ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ ↑ a ; E ? {{ v , Q } }" := (wp (MaybeStuck,a) E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' ↑ a ;  '/' E ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ ↑ a {{ v , Q } }" := (wp (NotStuck,a) ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  ↑ a  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ ↑ a ? {{ v , Q } }" := (wp (MaybeStuck,a) ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  ↑ a  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; ↑ a ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; ↑ a; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' ↑ a ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑ a ; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ↑ a ;  '/' E ']'  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a ; E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑ a ; E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ↑ a ;  '/' E ']'  '/' ? {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑ a {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  ↑ a  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑ a ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  ↑ a  '/' ? {{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ s ; ↑ a ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ s; ↑a; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' ↑ a ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ↑ a ;  '/' E ']'  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a ; E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a; E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' ↑ a ;  '/' E ']'  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  @  ↑ a  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ ↑ a ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  ↑ a  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; ↑ a ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; ↑a; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑a; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a ; E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑a; E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑a {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ ↑a ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ s ; ↑ a ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ s; ↑a; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a ; E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a; E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑a {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ ↑ a ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ ■ (Q -∗ Φ pat%V) -∗ WP e @ ↑ a ?{{ Φ }}) : stdpp_scope.
