import Hindman168.CosetSectionCountingLift
import Hindman168.MeasurableTransversalEquivalence

/-! Original left action permutes the actual lattice sheets. Genuine
periodization and invariant base measure imply invariant counting lift. -/

namespace Hindman168
open MeasureTheory
open scoped ENNReal

theorem coset_section_periodization_translation {G : Type*} [Group G]
    (Γ : Subgroup G) (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q)
    (f : G → ℝ≥0∞) (g : G) (q : G ⧸ Γ) :
    (∑' γ : Γ, f (g*(τ q*(γ : G)))) = ∑' γ : Γ, f (τ (g • q)*(γ : G)) := by
  have hq : (g*τ q : G ⧸ Γ) = g • q := by
    change g • (τ q : G ⧸ Γ) = g • q
    rw [hτ]
  let δ : Γ := ⟨(τ (g • q))⁻¹*(g*τ q), QuotientGroup.eq.mp ((hτ (g • q)).trans hq.symm)⟩
  have he : ∀ γ : Γ, g*(τ q*(γ : G)) = τ (g • q)*(↑(δ*γ) : G) := by
    intro γ
    change g*(τ q*(γ : G)) = τ (g • q)*(((τ (g • q))⁻¹*(g*τ q))*(γ : G))
    group
  simp_rw [he]
  exact (Equiv.mulLeft δ).tsum_eq (fun γ : Γ => f (τ (g • q)*(γ : G)))

theorem coset_section_counting_lift_leftInvariant {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSingletonClass G]
    (Γ : Subgroup G) [Countable Γ] [MeasurableConstSMul G (G ⧸ Γ)]
    (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (hmτ : Measurable τ)
    (ν : Measure (G ⧸ Γ)) (hν : ∀ g : G, Measure.map (fun q : G ⧸ Γ => g • q) ν = ν) :
    Measure.IsMulLeftInvariant (cosetSectionCountingLift Γ τ hτ hmτ ν) := by
  constructor
  intro g
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_const_mul g),
    coset_section_counting_lift_lintegral Γ τ hτ hmτ ν (fun x => f (g*x))
      (hf.comp (measurable_const_mul g)), coset_section_counting_lift_lintegral Γ τ hτ hmτ ν f hf]
  simp_rw [coset_section_periodization_translation Γ τ hτ f g]
  let S := fun q : G ⧸ Γ => ∑' γ : Γ, f (τ q*(γ : G))
  have hS : Measurable S := Measurable.tsum (fun γ : Γ => hf.comp (hmτ.mul_const (γ : G)))
  calc
    _ = ∫⁻ q, S q ∂Measure.map (fun q : G ⧸ Γ => g • q) ν :=
      (lintegral_map hS (measurable_const_smul g)).symm
    _ = _ := by rw [hν]

end Hindman168
