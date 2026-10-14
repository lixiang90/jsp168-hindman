import Hindman168.CosetSectionTransversal
import Hindman168.CosetSectionCountingLift

/-! Actual counting lift restricted to the actual transversal recovers the
ORIGINAL base measure, without invariant-measure or normality assumptions. -/

namespace Hindman168
open Set MeasureTheory
open scoped ENNReal Classical

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSingletonClass G]

theorem coset_section_counting_lift_transversal_preimage (Γ : Subgroup G) [Countable Γ]
    (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (F : Set G) (hF : MeasurableSet F) (hinj : F.InjOn ((↑) : G → G ⧸ Γ))
    (hτF : ∀ q, τ q ∈ F) (ν : Measure (G ⧸ Γ)) (A : Set (G ⧸ Γ)) (hA : MeasurableSet A) :
    cosetSectionCountingLift Γ τ hτ hmτ ν (((↑) : G → G ⧸ Γ) ⁻¹' A ∩ F) = ν A := by
  have hπ : Measurable ((↑) : G → G ⧸ Γ) := QuotientGroup.measurable_coe
  rw [coset_section_counting_lift_apply Γ τ hτ hmτ ν _ ((hπ hA).inter hF)]
  have hc : ∀ q : G ⧸ Γ, Measure.count {γ : Γ | τ q*(γ : G) ∈
      (((↑) : G → G ⧸ Γ) ⁻¹' A ∩ F)} = A.indicator (fun _ => (1 : ℝ≥0∞)) q := by
    intro q
    have hs : {γ : Γ | τ q*(γ : G) ∈ (((↑) : G → G ⧸ Γ) ⁻¹' A ∩ F)} =
        if q ∈ A then {1} else ∅ := by
      ext γ
      simp only [Set.mem_setOf_eq, coset_section_transversal_fiber_iff Γ τ hτ F hinj hτF]
      by_cases hq : q ∈ A <;> simp [hq]
    rw [hs]
    by_cases hq : q ∈ A <;> simp [hq]
  simp_rw [hc]
  exact lintegral_indicator_one hA

theorem coset_section_counting_lift_transversal_mass (Γ : Subgroup G) [Countable Γ]
    (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (F : Set G) (hF : MeasurableSet F) (hinj : F.InjOn ((↑) : G → G ⧸ Γ))
    (hτF : ∀ q, τ q ∈ F) (ν : Measure (G ⧸ Γ)) :
    cosetSectionCountingLift Γ τ hτ hmτ ν F = ν Set.univ := by
  simpa only [Set.preimage_univ, Set.univ_inter] using
    coset_section_counting_lift_transversal_preimage Γ τ hτ hmτ F hF hinj hτF ν Set.univ MeasurableSet.univ

theorem coset_section_counting_lift_transversal_map (Γ : Subgroup G) [Countable Γ]
    (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (F : Set G) (hF : MeasurableSet F) (hinj : F.InjOn ((↑) : G → G ⧸ Γ))
    (hτF : ∀ q, τ q ∈ F) (ν : Measure (G ⧸ Γ)) :
    Measure.map ((↑) : G → G ⧸ Γ) ((cosetSectionCountingLift Γ τ hτ hmτ ν).restrict F) = ν := by
  ext A hA
  have hπ : Measurable ((↑) : G → G ⧸ Γ) := QuotientGroup.measurable_coe
  rw [Measure.map_apply hπ hA, Measure.restrict_apply (hπ hA)]
  exact coset_section_counting_lift_transversal_preimage Γ τ hτ hmτ F hF hinj hτF ν A hA

end Hindman168
