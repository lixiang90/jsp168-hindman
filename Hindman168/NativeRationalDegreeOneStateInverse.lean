import Hindman168.NativeRationalDegreeOneFiniteVariablesInverse
import Hindman168.NativeRationalWeightedPolynomialState

/-! The NONZERO degree-one inverse is actually applied to the TRUE Unit-
variable coefficient polynomial of an actual recursive native state. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_one_actual_state_inverse {s : ℕ}
    (S : NativeRationalWeightedPolynomialState.{u} s 1) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace S.1.E := borel S.1.E
    letI : MeasurableSpace S.1.G := borel S.1.G
    letI := S.1.metric
    letI : TopologicalSpace (S.1.G ⧸ S.1.Γ) := S.1.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, 0 < N →
      ∀ H ∈ unitLipschitzObservables (S.1.G ⧸ S.1.Γ),
        δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy S.1 (scalarMvIntegerCube Unit N)
          (nativeMvPolynomialOrbit S.1 S.2.2.val) H‖ →
        ∃ χ : S.1.E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := S.1.I) S.1.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := S.1.I) S.1.Γ (M : ℝ) ∧
          (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap S.2.2.val) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
          ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap S.2.2.val) 1 J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace S.1.E := borel S.1.E
  letI : MeasurableSpace S.1.G := borel S.1.G
  letI := S.1.metric
  letI : TopologicalSpace (S.1.G ⧸ S.1.Γ) := S.1.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,hM,hInverse⟩ := native_rational_degree_one_finite_variables_inverse S.1 S.2.1 Unit δ hδ
  exact ⟨M,hM,hInverse S.2.2.val S.2.2.property.1⟩

end Hindman168
