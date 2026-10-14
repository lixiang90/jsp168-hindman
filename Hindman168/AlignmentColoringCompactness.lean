import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-! The compact coloring-space reduction in the finite Alignment plan.
The pointwise recurrence premise is explicit; this file proves its uniform
finite consequence, without claiming polynomial recurrence existence. -/

namespace Hindman168
open scoped Classical

def alignmentColoringSuccess {H W Color : Type*} [Group H]
    (words : Finset W) (curve : W → ℕ → H) (p : ℕ × H)
    (χ : H → Color) : Prop :=
  0 < p.1 ∧ ∀ w ∈ words, χ p.2 = χ (curve w p.1 * p.2)

theorem alignmentColoringSuccess_isOpen {H W Color : Type*} [Group H]
    [TopologicalSpace Color] [DiscreteTopology Color]
    (words : Finset W) (curve : W → ℕ → H) (p : ℕ × H) :
    IsOpen {χ : H → Color | alignmentColoringSuccess words curve p χ} := by
  by_cases hp : 0 < p.1
  · have hEq (w : W) :
        IsOpen {χ : H → Color | χ p.2 = χ (curve w p.1 * p.2)} := by
      have hCoordinate (g : H) (c : Color) :
          IsOpen {χ : H → Color | χ g = c} := by
        have hc : Continuous (fun χ : H → Color => χ g) := continuous_apply g
        have ho : IsOpen ({c} : Set Color) := isOpen_discrete _
        exact IsOpen.preimage hc ho
      have hUnion := isOpen_iUnion (fun c : Color =>
        (hCoordinate p.2 c).inter (hCoordinate (curve w p.1 * p.2) c))
      have hSet : (⋃ c : Color, {χ : H → Color | χ p.2 = c} ∩
          {χ : H → Color | χ (curve w p.1 * p.2) = c}) =
          {χ : H → Color | χ p.2 = χ (curve w p.1 * p.2)} := by
        ext χ
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
        exact ⟨fun ⟨c, h₁, h₂⟩ => h₁.trans h₂.symm,
          fun h => ⟨χ p.2, rfl, h.symm⟩⟩
      exact hSet ▸ hUnion
    have h := isOpen_biInter_finset (s := words) (fun w _ => hEq w)
    have hSet : (⋂ w ∈ words,
        {χ : H → Color | χ p.2 = χ (curve w p.1 * p.2)}) =
        {χ : H → Color | alignmentColoringSuccess words curve p χ} := by
      ext χ
      simp only [Set.mem_iInter, Set.mem_setOf_eq, alignmentColoringSuccess,
        hp, true_and]
    exact hSet ▸ h
  · have hEmpty : {χ : H → Color | alignmentColoringSuccess words curve p χ} = ∅ := by
      ext χ
      simp only [Set.mem_setOf_eq, alignmentColoringSuccess, hp, false_and,
        Set.mem_empty_iff_false]
    rw [hEmpty]
    exact isOpen_empty

theorem alignment_finite_coloring_alternatives {H W Color : Type*} [Group H]
    [Finite Color] (words : Finset W) (curve : W → ℕ → H)
    (hrec : ∀ χ : H → Color, ∃ k J,
      0 < k ∧ ∀ w ∈ words, χ J = χ (curve w k * J)) :
    ∃ alternatives : Finset (ℕ × H),
      (∀ p ∈ alternatives, 0 < p.1) ∧
      ∀ χ : H → Color, ∃ p ∈ alternatives,
        ∀ w ∈ words, χ p.2 = χ (curve w p.1 * p.2) := by
  letI : TopologicalSpace Color := ⊥
  letI : DiscreteTopology Color := discreteTopology_bot Color
  let U (p : ℕ × H) := {χ : H → Color | alignmentColoringSuccess words curve p χ}
  have hcover : (Set.univ : Set (H → Color)) ⊆ ⋃ p, U p := by
    intro χ _
    obtain ⟨k, J, hk, hχ⟩ := hrec χ
    exact Set.mem_iUnion.mpr ⟨(k, J), hk, hχ⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun p => alignmentColoringSuccess_isOpen words curve p) hcover
  refine ⟨t.filter (fun p => 0 < p.1), ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro χ
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ χ))
    obtain ⟨hpt, hpχ⟩ := Set.mem_iUnion.mp hp
    exact ⟨p, Finset.mem_filter.mpr ⟨hpt, hpχ.1⟩, hpχ.2⟩

end Hindman168
