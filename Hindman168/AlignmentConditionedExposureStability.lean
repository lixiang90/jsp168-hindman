import Hindman168.AlignmentShortExposureKey
import Hindman168.AlignmentRawArrayStability
import Hindman168.FiniteExposureEventDisintegration

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

theorem alignment_conditioned_array_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ))
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ j ∈ T, j < i)
    (G : ℕ → (Fin n → ℕ) → Prop) {c : ℝ} (hc : 0 < c)
    (hG : ∀ᶠ w in atTop, c ≤ event (globalRawMass (F.cutoff w) (primorial w) n) (G w)) :
    Tendsto (fun w => event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n) (G w))
      (fun x => ¬ alignmentRawArrayStable F w i q₀ V U S x)) atTop (𝓝 0) := by
  exact finite_positive_conditioning_zero_limit _ _ _
    ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => h.1)) hc hG
    (alignment_raw_array_failure_tendsto hF i q₀ V U S hS)

theorem alignment_shortExposure_array_bad_fiber_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ))
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ j ∈ T, j < i)
    (T : Finset (Fin n)) (G : ℕ → (Fin n → ℕ) → Prop) {c ε : ℝ} (hc : 0 < c)
    (hG : ∀ᶠ w in atTop, c ≤ event (globalRawMass (F.cutoff w) (primorial w) n) (G w))
    (hε : 0 < ε) :
    Tendsto (fun w =>
      let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) n) (G w)
      event (μ.mapDomain (alignmentShortExposureKey F w i T))
        (fun y => ε ≤ event (conditionMass μ (fun x => alignmentShortExposureKey F w i T x = y))
          (fun x => ¬ alignmentRawArrayStable F w i q₀ V U S x))) atTop (𝓝 0) := by
  apply finite_exposure_bad_fiber_tendsto _ _ _ _
    (alignment_conditioned_array_failure_tendsto hF i q₀ V U S hS G hc hG) hε
  filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
  exact conditionMass_nonneg _ _ hw.1

end Hindman168
