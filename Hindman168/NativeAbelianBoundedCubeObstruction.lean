import Hindman168.NativeAbelianBinomialObstruction
import Hindman168.BoundedComplexObservableNormalization

namespace Hindman168
open MeasureTheory Module
open scoped Classical BigOperators Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

/-- Fixed original sup and Lipschitz bounds are normalized before all
polynomials, lengths and observables, retaining the SAME original character. -/
theorem native_abelian_bounded_cube_obstruction
    (D : NativeNilmanifoldData.{u} 1) (n d : ℕ) (B : ℝ) (L : NNReal) (η : ℝ) (hη : 0 < η) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∃ M : ℕ, 0 < M ∧ ∀ (Q : (Fin n → ℝ) → D.G) (p : RoughVectorMvPolynomial (Fin n) D.E),
      RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
        ∀ N : ℕ, 0 < N → ∀ F : C(D.G ⧸ D.Γ, ℂ),
          LipschitzWith L F → (∀ q, ‖F q‖ ≤ B) →
          η ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
            (fun x => F (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) - ∫ q, F q ∂nativeAbelianTorusHaar D‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) d J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  let R : ℝ := max 1 (max B (L : ℝ))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hBR : B ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hLR : (L : ℝ) ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hδ : 0 < η/R := div_pos hη hR
  obtain ⟨M, hM, hinv⟩ := native_abelian_binomial_observable_obstruction D n d (η/R) hδ
  refine ⟨M, hM, ?_⟩
  intro Q p hp hQ N hN F hF hbound hbad
  have hunit := bounded_complex_observable_normalization F B R L hR hBR hLR hF hbound
  have hnorm : ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
      (fun x => (R⁻¹ • F) (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) -
      ∫ q, (R⁻¹ • F) q ∂nativeAbelianTorusHaar D‖ =
      R⁻¹*‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
        (fun x => F (Q (fun i => (x i : ℝ)) : D.G ⧸ D.Γ)) - ∫ q, F q ∂nativeAbelianTorusHaar D‖ := by
    simp only [ContinuousMap.smul_apply]
    rw [finite_haar_discrepancy_real_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hR.le)]
  apply hinv Q p hp hQ N hN (R⁻¹ • F) hunit
  rw [hnorm, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hbad (inv_nonneg.mpr hR.le)

end Hindman168
