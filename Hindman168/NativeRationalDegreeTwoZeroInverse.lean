import Hindman168.NativeRationalZeroInverseNatReduction

/-! COMPLETE true degree-TWO ZERO-FREQUENCY branch: ACTUAL degree-one child
inverse is PROVED and its ACTUALLY NONZERO character is pulled back to the
ORIGINAL group/lattice with fixed grid/operator/monomial/binomial bounds.
The nonzero-frequency branch and full degree-two inverse remain open. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_two_zero_mode_inverse {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 2)
    (σ : Type*) [Fintype σ]
 (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial σ D.E,
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
        ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N)
            (nativeMvPolynomialOrbit D p) (nativeRationalTerminalFourierProjection D L 0 H)‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) 2 J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  exact native_rational_zero_inverse_nat_reduction D L σ
    (native_rational_weighted_inverse_degree_one (nativeRationalTerminalQuotientData D L)
      (nativeTerminalRationalLieFiltration D L) σ) η hη

end Hindman168
