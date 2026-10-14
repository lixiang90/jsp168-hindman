import Hindman168.CosetSectionCoordinates
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Actual coset measure lifting along lattice counting, using a PROVED
measurable section decomposition rather than a normal quotient group. -/

namespace Hindman168
open MeasureTheory
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

noncomputable def cosetSectionCountingLift (Γ : Subgroup G) (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ) (ν : Measure (G ⧸ Γ)) : Measure G :=
  Measure.map (cosetSectionMeasurableEquiv Γ τ hτ hmτ) (ν.prod Measure.count)

theorem coset_section_counting_lift_sigmaFinite [MeasurableSingletonClass G]
    (Γ : Subgroup G) [Countable Γ] (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ) (ν : Measure (G ⧸ Γ)) [SigmaFinite ν] :
    SigmaFinite (cosetSectionCountingLift Γ τ hτ hmτ ν) :=
  (cosetSectionMeasurableEquiv Γ τ hτ hmτ).sigmaFinite_map

theorem coset_section_counting_lift_apply [MeasurableSingletonClass G]
    (Γ : Subgroup G) [Countable Γ] (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ) (ν : Measure (G ⧸ Γ))
    (A : Set G) (hA : MeasurableSet A) :
    cosetSectionCountingLift Γ τ hτ hmτ ν A =
      ∫⁻ q : G ⧸ Γ, Measure.count {γ : Γ | τ q*(γ : G) ∈ A} ∂ν := by
  rw [cosetSectionCountingLift, Measure.map_apply
    (cosetSectionMeasurableEquiv Γ τ hτ hmτ).measurable hA]
  rw [Measure.prod_apply ((cosetSectionMeasurableEquiv Γ τ hτ hmτ).measurable hA)]
  rfl

theorem coset_section_counting_lift_lintegral [MeasurableSingletonClass G]
    (Γ : Subgroup G) [Countable Γ] (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ) (ν : Measure (G ⧸ Γ))
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂cosetSectionCountingLift Γ τ hτ hmτ ν) =
      ∫⁻ q : G ⧸ Γ, ∑' γ : Γ, f (τ q*(γ : G)) ∂ν := by
  rw [cosetSectionCountingLift, lintegral_map hf
    (cosetSectionMeasurableEquiv Γ τ hτ hmτ).measurable]
  have ht := lintegral_prod (μ := ν) (ν := (Measure.count : Measure Γ))
    (f ∘ cosetSectionMeasurableEquiv Γ τ hτ hmτ)
    (hf.comp (cosetSectionMeasurableEquiv Γ τ hτ hmτ).measurable).aemeasurable
  calc
    _ = ∫⁻ q : G ⧸ Γ, ∫⁻ γ : Γ,
        f (cosetSectionMeasurableEquiv Γ τ hτ hmτ (q,γ)) ∂Measure.count ∂ν := ht
    _ = _ := by
      simp only [lintegral_count]
      rfl

end Hindman168
