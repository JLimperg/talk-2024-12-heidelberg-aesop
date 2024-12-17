/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Separation.Basic

/-!
# Topology on the set of filters on a type

This file introduces a topology on `Filter α`. It is generated by the sets
`Set.Iic (𝓟 s) = {l : Filter α | s ∈ l}`, `s : Set α`. A set `s : Set (Filter α)` is open if and
only if it is a union of a family of these basic open sets, see `Filter.isOpen_iff`.

This topology has the following important properties.

* If `X` is a topological space, then the map `𝓝 : X → Filter X` is a topology inducing map.

* In particular, it is a continuous map, so `𝓝 ∘ f` tends to `𝓝 (𝓝 a)` whenever `f` tends to `𝓝 a`.

* If `X` is an ordered topological space with order topology and no max element, then `𝓝 ∘ f` tends
  to `𝓝 Filter.atTop` whenever `f` tends to `Filter.atTop`.

* It turns `Filter X` into a T₀ space and the order on `Filter X` is the dual of the
  `specializationOrder (Filter X)`.

## Tags

filter, topological space
-/


open Set Filter TopologicalSpace

open Filter Topology

variable {ι : Sort*} {α β X Y : Type*}

namespace Filter

/-- The topology on `Filter α` is generated by the sets `Set.Iic (𝓟 s) = {l : Filter α | s ∈ l}`,
`s : Set α`. A set `s : Set (Filter α)` is open if and only if it is a union of a family of these
basic open sets, see `Filter.isOpen_iff`. -/
instance : TopologicalSpace (Filter α) :=
  generateFrom <| range <| Iic ∘ 𝓟

theorem isOpen_Iic_principal {s : Set α} : IsOpen (Iic (𝓟 s)) :=
  GenerateOpen.basic _ (mem_range_self _)

theorem isOpen_setOf_mem {s : Set α} : IsOpen { l : Filter α | s ∈ l } := by
  simpa only [Iic_principal] using isOpen_Iic_principal

theorem isTopologicalBasis_Iic_principal :
    IsTopologicalBasis (range (Iic ∘ 𝓟 : Set α → Set (Filter α))) :=
  { exists_subset_inter := by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ l hl
      exact ⟨Iic (𝓟 s) ∩ Iic (𝓟 t), ⟨s ∩ t, by simp⟩, hl, Subset.rfl⟩
    sUnion_eq := sUnion_eq_univ_iff.2 fun _ => ⟨Iic ⊤, ⟨univ, congr_arg Iic principal_univ⟩,
      mem_Iic.2 le_top⟩
    eq_generateFrom := rfl }

theorem isOpen_iff {s : Set (Filter α)} : IsOpen s ↔ ∃ T : Set (Set α), s = ⋃ t ∈ T, Iic (𝓟 t) :=
  isTopologicalBasis_Iic_principal.open_iff_eq_sUnion.trans <| by
    simp only [exists_subset_range_and_iff, sUnion_image, (· ∘ ·)]

theorem nhds_eq (l : Filter α) : 𝓝 l = l.lift' (Iic ∘ 𝓟) :=
  nhds_generateFrom.trans <| by
    simp only [mem_setOf_eq, @and_comm (l ∈ _), iInf_and, iInf_range, Filter.lift', Filter.lift,
      (· ∘ ·), mem_Iic, le_principal_iff]

theorem nhds_eq' (l : Filter α) : 𝓝 l = l.lift' fun s => { l' | s ∈ l' } := by
  simpa only [Function.comp_def, Iic_principal] using nhds_eq l

protected theorem tendsto_nhds {la : Filter α} {lb : Filter β} {f : α → Filter β} :
    Tendsto f la (𝓝 lb) ↔ ∀ s ∈ lb, ∀ᶠ a in la, s ∈ f a := by
  simp only [nhds_eq', tendsto_lift', mem_setOf_eq]

protected theorem HasBasis.nhds {l : Filter α} {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis (𝓝 l) p fun i => Iic (𝓟 (s i)) := by
  rw [nhds_eq]
  exact h.lift' monotone_principal.Iic

protected theorem tendsto_pure_self (l : Filter X) :
    Tendsto (pure : X → Filter X) l (𝓝 l) := by
  rw [Filter.tendsto_nhds]
  exact fun s hs ↦ Eventually.mono hs fun x ↦ id

/-- Neighborhoods of a countably generated filter is a countably generated filter. -/
instance {l : Filter α} [IsCountablyGenerated l] : IsCountablyGenerated (𝓝 l) :=
  let ⟨_b, hb⟩ := l.exists_antitone_basis
  HasCountableBasis.isCountablyGenerated <| ⟨hb.nhds, Set.to_countable _⟩

theorem HasBasis.nhds' {l : Filter α} {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis (𝓝 l) p fun i => { l' | s i ∈ l' } := by simpa only [Iic_principal] using h.nhds

protected theorem mem_nhds_iff {l : Filter α} {S : Set (Filter α)} :
    S ∈ 𝓝 l ↔ ∃ t ∈ l, Iic (𝓟 t) ⊆ S :=
  l.basis_sets.nhds.mem_iff

theorem mem_nhds_iff' {l : Filter α} {S : Set (Filter α)} :
    S ∈ 𝓝 l ↔ ∃ t ∈ l, ∀ ⦃l' : Filter α⦄, t ∈ l' → l' ∈ S :=
  l.basis_sets.nhds'.mem_iff

@[simp]
theorem nhds_bot : 𝓝 (⊥ : Filter α) = pure ⊥ := by
  simp [nhds_eq, Function.comp_def, lift'_bot monotone_principal.Iic]

@[simp]
theorem nhds_top : 𝓝 (⊤ : Filter α) = ⊤ := by simp [nhds_eq]

@[simp]
theorem nhds_principal (s : Set α) : 𝓝 (𝓟 s) = 𝓟 (Iic (𝓟 s)) :=
  (hasBasis_principal s).nhds.eq_of_same_basis (hasBasis_principal _)

@[simp]
theorem nhds_pure (x : α) : 𝓝 (pure x : Filter α) = 𝓟 {⊥, pure x} := by
  rw [← principal_singleton, nhds_principal, principal_singleton, Iic_pure]

@[simp]
theorem nhds_iInf (f : ι → Filter α) : 𝓝 (⨅ i, f i) = ⨅ i, 𝓝 (f i) := by
  simp only [nhds_eq]
  apply lift'_iInf_of_map_univ <;> simp

@[simp]
theorem nhds_inf (l₁ l₂ : Filter α) : 𝓝 (l₁ ⊓ l₂) = 𝓝 l₁ ⊓ 𝓝 l₂ := by
  simpa only [iInf_bool_eq] using nhds_iInf fun b => cond b l₁ l₂

theorem monotone_nhds : Monotone (𝓝 : Filter α → Filter (Filter α)) :=
  Monotone.of_map_inf nhds_inf

theorem sInter_nhds (l : Filter α) : ⋂₀ { s | s ∈ 𝓝 l } = Iic l := by
  simp_rw [nhds_eq, Function.comp_def, sInter_lift'_sets monotone_principal.Iic, Iic,
    le_principal_iff, ← setOf_forall, ← Filter.le_def]

@[simp]
theorem nhds_mono {l₁ l₂ : Filter α} : 𝓝 l₁ ≤ 𝓝 l₂ ↔ l₁ ≤ l₂ := by
  refine ⟨fun h => ?_, fun h => monotone_nhds h⟩
  rw [← Iic_subset_Iic, ← sInter_nhds, ← sInter_nhds]
  exact sInter_subset_sInter h

protected theorem mem_interior {s : Set (Filter α)} {l : Filter α} :
    l ∈ interior s ↔ ∃ t ∈ l, Iic (𝓟 t) ⊆ s := by
  rw [mem_interior_iff_mem_nhds, Filter.mem_nhds_iff]

protected theorem mem_closure {s : Set (Filter α)} {l : Filter α} :
    l ∈ closure s ↔ ∀ t ∈ l, ∃ l' ∈ s, t ∈ l' := by
  simp only [closure_eq_compl_interior_compl, Filter.mem_interior, mem_compl_iff, not_exists,
    not_forall, Classical.not_not, exists_prop, not_and, and_comm, subset_def, mem_Iic,
    le_principal_iff]

@[simp]
protected theorem closure_singleton (l : Filter α) : closure {l} = Ici l := by
  ext l'
  simp [Filter.mem_closure, Filter.le_def]

@[simp]
theorem specializes_iff_le {l₁ l₂ : Filter α} : l₁ ⤳ l₂ ↔ l₁ ≤ l₂ := by
  simp only [specializes_iff_closure_subset, Filter.closure_singleton, Ici_subset_Ici]

instance : T0Space (Filter α) :=
  ⟨fun _ _ h => (specializes_iff_le.1 h.specializes).antisymm
    (specializes_iff_le.1 h.symm.specializes)⟩

theorem nhds_atTop [Preorder α] : 𝓝 atTop = ⨅ x : α, 𝓟 (Iic (𝓟 (Ici x))) := by
  simp only [atTop, nhds_iInf, nhds_principal]

protected theorem tendsto_nhds_atTop_iff [Preorder β] {l : Filter α} {f : α → Filter β} :
    Tendsto f l (𝓝 atTop) ↔ ∀ y, ∀ᶠ a in l, Ici y ∈ f a := by
  simp only [nhds_atTop, tendsto_iInf, tendsto_principal, mem_Iic, le_principal_iff]

theorem nhds_atBot [Preorder α] : 𝓝 atBot = ⨅ x : α, 𝓟 (Iic (𝓟 (Iic x))) :=
  @nhds_atTop αᵒᵈ _

protected theorem tendsto_nhds_atBot_iff [Preorder β] {l : Filter α} {f : α → Filter β} :
    Tendsto f l (𝓝 atBot) ↔ ∀ y, ∀ᶠ a in l, Iic y ∈ f a :=
  @Filter.tendsto_nhds_atTop_iff α βᵒᵈ _ _ _

variable [TopologicalSpace X]

theorem nhds_nhds (x : X) :
    𝓝 (𝓝 x) = ⨅ (s : Set X) (_ : IsOpen s) (_ : x ∈ s), 𝓟 (Iic (𝓟 s)) := by
  simp only [(nhds_basis_opens x).nhds.eq_biInf, iInf_and, @iInf_comm _ (_ ∈ _)]

theorem isInducing_nhds : IsInducing (𝓝 : X → Filter X) :=
  isInducing_iff_nhds.2 fun x =>
    (nhds_def' _).trans <| by
      simp +contextual only [nhds_nhds, comap_iInf, comap_principal,
        Iic_principal, preimage_setOf_eq, ← mem_interior_iff_mem_nhds, setOf_mem_eq,
        IsOpen.interior_eq]

@[deprecated (since := "2024-10-28")] alias inducing_nhds := isInducing_nhds

@[continuity]
theorem continuous_nhds : Continuous (𝓝 : X → Filter X) :=
  isInducing_nhds.continuous

protected theorem Tendsto.nhds {f : α → X} {l : Filter α} {x : X} (h : Tendsto f l (𝓝 x)) :
    Tendsto (𝓝 ∘ f) l (𝓝 (𝓝 x)) :=
  (continuous_nhds.tendsto _).comp h

end Filter

variable [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {x : X} {s : Set X}

protected nonrec theorem ContinuousWithinAt.nhds (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (𝓝 ∘ f) s x :=
  h.nhds

protected nonrec theorem ContinuousAt.nhds (h : ContinuousAt f x) : ContinuousAt (𝓝 ∘ f) x :=
  h.nhds

protected nonrec theorem ContinuousOn.nhds (h : ContinuousOn f s) : ContinuousOn (𝓝 ∘ f) s :=
  fun x hx => (h x hx).nhds

protected nonrec theorem Continuous.nhds (h : Continuous f) : Continuous (𝓝 ∘ f) :=
  Filter.continuous_nhds.comp h