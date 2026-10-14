import Hindman168.NativeRationalInverseBoundedAlternative
import Hindman168.NativeRationalDegreeTwoZeroInverse

/-! TRUE degree-two alternative with NO child inverse hypothesis: original
NONZERO horizontal obstruction OR bounded original nonzero terminal mode.
The second alternative remains to be resolved; this is NOT the full inverse. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_two_inverse_bounded_alternative {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 2)
    (σ : Type*) [Fintype σ]
 (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ M : ℕ, 0 < M ∧ ∃ S : Finset (nativeRationalTerminalIndex D L → ℤ),
      (∀ k ∈ S, (∑ i, (k i).natAbs) ≤ M) ∧
      ∀ p : RoughVectorMvPolynomial σ D.E, RoughVectorMvWeightedDegree L.layer p 0 →
        ∀ N : ℕ, 0 < N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H‖ →
          (∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) 2 J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∨
          ∃ k ∈ S, k ≠ 0 ∧ η ≤ ‖finiteComplexSetMean (scalarMvIntegerCube σ N)
            (fun x => nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p x))‖ := by
  exact native_rational_inverse_bounded_alternative D L σ
    (native_rational_weighted_inverse_degree_one (nativeRationalTerminalQuotientData D L)
      (nativeTerminalRationalLieFiltration D L) σ) δ hδ

end Hindman168
