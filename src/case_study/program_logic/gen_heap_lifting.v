From iris.base_logic Require Export gen_heap.
From iris.algebra Require Export list excl_auth.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From nextgen Require Import nextgen_basic nextgen_pointwise.
Set Default Proof Using "Type".
Import uPred.

(** Some useful typeclasses for using IndInG/NoInG with gen_heaps and ghost_map *)

Class ghost_mapIndG (Σ : gFunctors) (Ω : gTransformations Σ) (K V : Type) (eqdec: EqDecision K) (count: @Countable K eqdec) : Set := GhostMapIndG
  { ghost_map_inIndG : genIndInG Σ Ω (gmap_view.gmap_viewR K (leibnizO V)) }.
Arguments ghost_mapIndG Σ Ω (K V)%type_scope {_ _}.
Arguments GhostMapIndG Σ Ω (K V)%type_scope {_ _ _}.

Class ghost_mapNoG (Σ : gFunctors) (Ω : gTransformations Σ) (K V : Type)  (eqdec: EqDecision K) (count: @Countable K eqdec) : Set := GhostMapNoG
  { ghost_map_inNoG : noTransInG Σ Ω (gmap_view.gmap_viewR K (leibnizO V)) }.
Arguments ghost_mapNoG Σ Ω (K V)%type_scope {_ _}.
Arguments GhostMapNoG Σ Ω (K V)%type_scope {_ _ _}.

Class gen_heapNoGpreS (L V : Type) (Σ : gFunctors) (Ω : gTransformations Σ) (eqdec: EqDecision L) (count: Countable L) : Set := Build_gen_heapNoGpreS
  { gen_heapNoGpreS_heap : ghost_mapNoG Σ Ω L V;
    gen_heapNoGpreS_meta : ghost_mapIndG Σ Ω L gname;
    gen_heapNoGpreS_meta_data : genIndInG Σ Ω (reservation_map.reservation_mapR (agreeR positiveO)) }.
Arguments gen_heapNoGpreS (L V)%type_scope Σ Ω {_ _}.
Arguments Build_gen_heapNoGpreS (L V)%type_scope Σ Ω {_ _ _ _ _}.

Class gen_heapIndGpreS (L V : Type) (Σ : gFunctors) (Ω : gTransformations Σ) (eqdec: EqDecision L) (count: Countable L) : Set := Build_gen_heapIndGpreS
  { gen_heapIndGpreS_heap : ghost_mapIndG Σ Ω L V;
    gen_heapIndGpreS_meta : ghost_mapIndG Σ Ω L gname;
    gen_heapIndGpreS_meta_data : genIndInG Σ Ω (reservation_map.reservation_mapR (agreeR positiveO)) }.
Arguments gen_heapIndGpreS (L V)%type_scope Σ Ω {_ _}.
Arguments Build_gen_heapIndGpreS (L V)%type_scope Σ Ω {_ _ _ _ _}.

Class gen_heapNoGS (L V : Type) (Σ : gFunctors) (Ω : gTransformations Σ) (eqdec: EqDecision L) (count: Countable L) : Set := GenHeapNoGS
  { gen_heap_inNoG : gen_heapNoGpreS L V Σ Ω;  no_gen_heap_name : gname;  no_gen_meta_name : gname }.
Arguments gen_heapNoGS (L V)%type_scope Σ Ω {_ _}.
Arguments GenHeapNoGS (L V)%type_scope Σ Ω {_ _ _} no_gen_heap_name no_gen_meta_name.

Class gen_heapIndGS (L V : Type) (Σ : gFunctors) (Ω : gTransformations Σ) (eqdec: EqDecision L) (count: Countable L) : Set := GenHeapIndGS
{ gen_heap_inIndG : gen_heapIndGpreS L V Σ Ω;  ind_gen_heap_name : gname;  ind_gen_meta_name : gname }.
Arguments gen_heapIndGS (L V)%type_scope Σ Ω {_ _}.
Arguments GenHeapIndGS (L V)%type_scope Σ Ω {_ _ _} ind_gen_heap_name ind_gen_meta_name.

Class gen_heapNoMetaGS (L V : Type) (Σ : gFunctors) (Ω : gTransformations Σ) (eqdec: EqDecision L) (count: Countable L) : Set := GenHeapNoMetaGS
  { gen_heap_inNoMetaG : ghost_mapNoG Σ Ω L V;  no_meta_gen_heap_name : gname; }.
Arguments gen_heapNoMetaGS (L V)%type_scope Σ Ω {_ _}.
Arguments GenHeapNoMetaGS (L V)%type_scope Σ Ω {_ _ _} no_meta_gen_heap_name.


(** Some coersions from above classes to gen_heap/ghost_map *)

#[global] Instance into_ghost_map_from_ind {K V Σ Ω} `{eqK: EqDecision K} `{countK: @Countable K eqK} (Hwsat: ghost_mapIndG Σ Ω K V) : ghost_map.ghost_mapG Σ K V :=
  ghost_map.GhostMapG Σ K V eqK countK (Hwsat.(ghost_map_inIndG)).(genInG_inG).
#[global] Instance into_ghost_map_from_no {K V Σ Ω} `{eqK: EqDecision K} `{countK: @Countable K eqK} (Hwsat: ghost_mapNoG Σ Ω K V) : ghost_map.ghost_mapG Σ K V :=
  ghost_map.GhostMapG Σ K V eqK countK (Hwsat.(ghost_map_inNoG)).(noTransInG_inG).

#[global] Instance into_gen_heap_pre_from_ind {L V Σ Ω} `{eqK: EqDecision L} `{countK: @Countable L eqK} (Hwsat: gen_heapIndGpreS L V Σ Ω) : gen_heapGpreS L V Σ :=
  Build_gen_heapGpreS L V Σ eqK countK (into_ghost_map_from_ind gen_heapIndGpreS_heap) (into_ghost_map_from_ind gen_heapIndGpreS_meta) gen_heapIndGpreS_meta_data.(genInG_inG).

#[global] Instance into_gen_heap_pre_from_no {L V Σ Ω} `{eqK: EqDecision L} `{countK: @Countable L eqK} (Hwsat: gen_heapNoGpreS L V Σ Ω) : gen_heapGpreS L V Σ :=
  Build_gen_heapGpreS L V Σ eqK countK (into_ghost_map_from_no gen_heapNoGpreS_heap) (into_ghost_map_from_ind gen_heapNoGpreS_meta) gen_heapNoGpreS_meta_data.(genInG_inG).

#[global] Instance into_gen_heap_from_ind {L V Σ Ω} `{eqK: EqDecision L} `{countK: @Countable L eqK} (Hwsat: gen_heapIndGS L V Σ Ω) : gen_heapGS L V Σ :=
  @GenHeapGS L V Σ eqK countK (into_gen_heap_pre_from_ind gen_heap_inIndG) ind_gen_heap_name ind_gen_meta_name.

#[global] Instance into_gen_heap_from_no {L V Σ Ω} `{eqK: EqDecision L} `{countK: @Countable L eqK} (Hwsat: gen_heapNoGS L V Σ Ω) : gen_heapGS L V Σ :=
  @GenHeapGS L V Σ eqK countK (into_gen_heap_pre_from_no gen_heap_inNoG) no_gen_heap_name no_gen_meta_name.


(** variants of gen_heap_init that take Ω into account *)

Lemma gen_heap_init_no_names `{Countable L, !gen_heapNoGpreS L V Σ Ω} σ :
  ⊢ |==> ∃ γh γm : gname,
    let hG := GenHeapNoGS L V Σ Ω γh γm in
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, mapsto l (DfracOwn 1) v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (ghost_map.ghost_map_alloc_empty (K:=L) (V:=V)) as (γh) "Hh".
  iMod (ghost_map.ghost_map_alloc_empty (K:=L) (V:=gname)) as (γm) "Hm".
  iExists γh, γm.
  iAssert (gen_heap_interp (hG:=GenHeapGS _ _ _ γh γm) ∅) with "[Hh Hm]" as "Hinterp".
  { iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L. }
  iMod (gen_heap_alloc_big with "Hinterp") as "(Hinterp & $ & $)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L. done.
Qed.

Lemma gen_heap_init_no `{Countable L, !gen_heapNoGpreS L V Σ Ω} σ :
  ⊢ |==> ∃ _ : gen_heapNoGS L V Σ Ω,
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, mapsto l (DfracOwn 1) v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (gen_heap_init_names σ) as (γh γm) "Hinit".
  iExists (GenHeapNoGS _ _ _ _ γh γm).
  done.
Qed.

Lemma gen_heap_init_ind `{Countable L, !gen_heapIndGpreS L V Σ Ω} σ :
  ⊢ |==> ∃ _ : gen_heapIndGS L V Σ Ω,
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, mapsto l (DfracOwn 1) v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (gen_heap_init_names σ) as (γh γm) "Hinit".
  iExists (GenHeapIndGS _ _ _ _ γh γm).
  done.
Qed.
