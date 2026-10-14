import Hindman168.DiscreteLatticeCompactSheets
import Hindman168.CosetSectionCountingLift

/-! Actual compact-range section and actual finite compact lattice
intersection prove the counting lift has finite mass on EVERY compact set. -/

namespace Hindman168
open Set MeasureTheory
open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]

theorem coset_section_counting_lift_compact_bound (Γ : Subgroup G) [Countable Γ]
    (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (ν : Measure (G ⧸ Γ)) [IsProbabilityMeasure ν]
    (K C : Set G) (hτK : Set.range τ ⊆ K) (hC : IsCompact C) :
    cosetSectionCountingLift Γ τ hτ hmτ ν C ≤
      Measure.count {γ : Γ | (γ : G) ∈ K⁻¹*C} := by
  rw [coset_section_counting_lift_apply Γ τ hτ hmτ ν C hC.measurableSet]
  calc
    _ ≤ ∫⁻ _q : G ⧸ Γ, Measure.count {γ : Γ | (γ : G) ∈ K⁻¹*C} ∂ν := by
      apply lintegral_mono
      intro q
      exact measure_mono (fun γ hγ => coset_section_compact_sheet_membership Γ τ K C hτK q γ hγ)
    _ = _ := by simp

theorem coset_section_counting_lift_compact_finite (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (hΓ : IsClosed (Γ : Set G)) (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (ν : Measure (G ⧸ Γ)) [IsProbabilityMeasure ν]
    (K C : Set G) (hK : IsCompact K) (hτK : Set.range τ ⊆ K) (hC : IsCompact C) :
    cosetSectionCountingLift Γ τ hτ hmτ ν C < ⊤ := by
  have hf := coset_section_compact_sheets_finite Γ hΓ K C hK hC
  apply lt_of_le_of_lt (coset_section_counting_lift_compact_bound Γ τ hτ hmτ ν K C hτK hC)
  rw [Measure.count_apply_finite _ hf]
  exact ENNReal.natCast_lt_top _

theorem coset_section_counting_lift_finiteOnCompacts (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (hΓ : IsClosed (Γ : Set G)) (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (ν : Measure (G ⧸ Γ)) [IsProbabilityMeasure ν]
    (K : Set G) (hK : IsCompact K) (hτK : Set.range τ ⊆ K) :
    IsFiniteMeasureOnCompacts (cosetSectionCountingLift Γ τ hτ hmτ ν) := by
  constructor
  intro C hC
  exact coset_section_counting_lift_compact_finite Γ hΓ τ hτ hmτ ν K C hK hτK hC

end Hindman168
