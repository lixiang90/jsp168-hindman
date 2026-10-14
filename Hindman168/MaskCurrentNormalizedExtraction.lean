import Hindman168.MaskAbsorbedDiagonalPositivity
import Hindman168.FiniteReplicaJointLaw

/-! Extract the current mask from the actual substituted correlation.
The eta multiplier enforces admissibility in the balanced case; the
unchanged current monomial and invariant density then sit outside the
fresh-prime average on the shared old-prime/base law. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

namespace MaskColumnPlan

variable {m : ℕ} {S U : Finset (Fin (m + 1))}

noncomputable def eta (P : MaskColumnPlan S U) (p : ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  match P with
  | .outside _ _ _ => 1
  | .balanced u _ _ _ _ _ _ => primeDivisorEta p (z u)

theorem eta_nonneg (P : MaskColumnPlan S U) (p : ℕ) (z : Fin (m + 1) → ℤ) :
    0 ≤ P.eta p z := by
  cases P
  · exact zero_le_one
  · exact primeDivisorEta_nonneg _ _

theorem admissible_of_eta_ne_zero (P : MaskColumnPlan S U) (p : ℕ)
    (z : Fin (m + 1) → ℤ) (h : P.eta p z ≠ 0) : P.admissible p z := by
  cases P with
  | outside u hu hU => trivial
  | balanced u v hu hv huU hvU hne =>
    by_contra hd
    exact h (if_neg hd)

end MaskColumnPlan

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskStageSubstitutedAverage (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun r =>
    expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
      (chosenMaskColumnPlan S U hS).eta p r.2 *
        H (r.1, (chosenMaskColumnPlan S U hS).coordinates p r.2)))

theorem maskRowMaskCorrelation_originalOuter (k w : ℕ) (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
      Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ) :
    maskRowMaskCorrelation gap C (maskPrefixRowStage S hS k).rows
      (masterColumnCoefficient N a (fun w => (C w).block) w) w T b f =
    expectation (maskStageOuterMass S hS gap C k w) (fun r =>
      maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
        (masterColumnCoefficient N a (fun w => (C w).block) w) f r.1 r.2 *
      maskMultiplicativeProduct T b r.1 r.2) := by
  rw [maskStageOuterMass, expectation_conditionalJoint]
  rfl

include hC htail in
theorem maskCurrentNormalizedExtraction_eventually_pointwise :
    ∀ᶠ w in atTop, ∀ k U T, U ∈ T →
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x z,
      (chosenMaskColumnPlan S U hS).eta p z *
        (maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
          (masterColumnCoefficient N a (fun w => (C w).block) w) f x
            ((chosenMaskColumnPlan S U hS).coordinates p z) *
         maskMultiplicativeProduct T b x ((chosenMaskColumnPlan S U hS).coordinates p z)) =
      b x U (maskCoordinateMonomial U z) * maskStageDensity S hS gap a C k U w (x,z) *
        ((chosenMaskColumnPlan S U hS).eta p z *
          maskStageNormalizedIntegrand S hS gap a C k U w (T.erase U) b f x
            ((chosenMaskColumnPlan S U hS).coordinates p z)) := by
  filter_upwards [maskStageNormalizedIntegrand_eventually_factorization S hS gap a C hC,
    maskStageInvariantDensity_preserved S hS gap a C hC htail] with w hf hd
  intro k U T hU p hp b f x z
  by_cases he : (chosenMaskColumnPlan S U hS).eta p z = 0
  · simp only [he, zero_mul, mul_zero]
  have ha := (chosenMaskColumnPlan S U hS).admissible_of_eta_ne_zero p z he
  rw [maskMultiplicativeProduct_erase T U hU,
    (chosenMaskColumnPlan S U hS).monomial_preserved p z ha]
  have hfact := hf k U (T.erase U) b f x ((chosenMaskColumnPlan S U hS).coordinates p z)
  have hdens := hd k U p hp x z ha
  calc
    _ = b x U (maskCoordinateMonomial U z) * (chosenMaskColumnPlan S U hS).eta p z *
      (maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
        (masterColumnCoefficient N a (fun w => (C w).block) w) f x
          ((chosenMaskColumnPlan S U hS).coordinates p z) *
       maskMultiplicativeProduct (T.erase U) b x ((chosenMaskColumnPlan S U hS).coordinates p z)) := by ring
    _ = _ := by rw [← hfact, hdens]; ring

include hC htail in
theorem maskCurrentNormalizedExtraction_eventually_average :
    ∀ᶠ w in atTop, ∀ k U T, U ∈ T →
      ∀ b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ,
      maskStageSubstitutedAverage S hS gap C k U w (fun r =>
        maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
          (masterColumnCoefficient N a (fun w => (C w).block) w) f r.1 r.2 *
        maskMultiplicativeProduct T b r.1 r.2) =
      expectation (maskStageOuterMass S hS gap C k w) (fun r =>
        b r.1 U (maskCoordinateMonomial U r.2) * maskStageDensity S hS gap a C k U w r *
          expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
            (chosenMaskColumnPlan S U hS).eta p r.2 *
              maskStageNormalizedIntegrand S hS gap a C k U w (T.erase U) b f r.1
                ((chosenMaskColumnPlan S U hS).coordinates p r.2))) := by
  filter_upwards [maskCurrentNormalizedExtraction_eventually_pointwise S hS gap a C hC htail] with w hw
  intro k U T hU b f
  unfold maskStageSubstitutedAverage
  apply congrArg (expectation _)
  funext r
  rw [← expectation_const_mul]
  apply expectation_congr_support
  intro p hp
  exact hw k U T hU p (primePoolMass_support _ _ hp) b f r.1 r.2

end Hindman168
