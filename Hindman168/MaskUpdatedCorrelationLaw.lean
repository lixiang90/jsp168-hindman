import Hindman168.MaskStageNormalizedIntegrands

/-! The updated correlation uses the complete original prime law and
unchanged harmonic base law. The exact averaged absorbed identity
retains diagonal pairs, which must be estimated separately in the
analytic mask recurrence. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N n r : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))

noncomputable def maskRowMaskCorrelation
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (c : Fin (m + 1) → ℕ) (w : ℕ) (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) : ℝ :=
  expectation (monomialRowPrimeMass m gap n w) (fun x =>
    expectation (maskOriginalBaseMass m gap C w) (fun z =>
      maskRowFunctionProduct F c f x z * maskMultiplicativeProduct T b x z))

theorem maskRowMaskCorrelation_freshLaw {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (c : Fin (m + 1) → ℕ) (w : ℕ) (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin n → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) :
    maskRowMaskCorrelation gap C (F.flattenedMaskStep P.tag) c w T
      (maskUpdatedMultiplicativeMasks P b) (maskUpdatedRowFunctions gap C P F w f) =
      expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (fun pq => expectation (monomialRowPrimeMass m gap n w) (fun x =>
          expectation (maskOriginalBaseMass m gap C w) (fun z =>
            maskRowFunctionProduct (F.flattenedMaskStep P.tag) c (maskUpdatedRowFunctions gap C P F w f)
              (maskFreshTuple x (P.freshValues pq.1 pq.2)) z *
            maskMultiplicativeProduct T (maskUpdatedMultiplicativeMasks P b)
              (maskFreshTuple x (P.freshValues pq.1 pq.2)) z))) := by
  exact maskFreshPrimeTupleLaw_expectation gap P w _

variable (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) (a : Fin (m + 1) → ℚ)
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

theorem maskStageFreshPairAverage_outerOrder (k w : ℕ)
    (H : MaskStagePoint S hS k → ℕ × ℕ → ℝ) :
    maskStageFreshPairAverage S hS gap C k w H =
      expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (fun pq => expectation (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w)
          (fun x => expectation (maskOriginalBaseMass m gap C w) (fun z => H (x,z) pq))) := by
  unfold maskStageFreshPairAverage
  rw [expectation_comm]
  apply congrArg (expectation _)
  funext pq
  rw [maskStageOuterMass, expectation_conditionalJoint]

include hC htail in
theorem maskRowMaskCorrelation_eventually_absorbedUpdate :
    ∀ᶠ w in atTop, ∀ k U T,
      ∀ b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ,
      maskRowMaskCorrelation gap C ((maskPrefixRowStage S hS k).step hS U).rows
        (masterColumnCoefficient N a (fun w => (C w).block) w) w T
        (maskUpdatedMultiplicativeMasks (chosenMaskColumnPlan S U hS) b)
        (maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS) (maskPrefixRowStage S hS k).rows w f) =
      maskStageFreshPairAverage S hS gap C k w (fun r pq =>
        maskStageDensity S hS gap a C k U w
          (r.1, (chosenMaskColumnPlan S U hS).absorptionCoordinates pq.1 pq.2 r.2) *
        maskStageNormalizedIntegrand S hS gap a C k U w T b f r.1
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates pq.1 pq.2 r.2) *
        maskStageNormalizedIntegrand S hS gap a C k U w T b f r.1
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates pq.2 pq.1 r.2)) := by
  filter_upwards [maskStageNormalizedIntegrand_eventually_absorbed_update S hS gap a C hC htail] with w hm
  intro k U T b f
  dsimp only [TargetedMaskRowStage.step]
  rw [maskRowMaskCorrelation_freshLaw, maskStageFreshPairAverage_outerOrder]
  apply expectation_congr_support
  intro pq hpq
  have hs := Finset.mem_product.mp (tensor_support _ _ hpq)
  have hp := primePoolMass_support _ _ hs.1
  have hq := primePoolMass_support _ _ hs.2
  apply congrArg (expectation _)
  funext x
  apply congrArg (expectation _)
  funext z
  exact (hm k U T pq.1 hp pq.2 hq b f x z).symm

end Hindman168
