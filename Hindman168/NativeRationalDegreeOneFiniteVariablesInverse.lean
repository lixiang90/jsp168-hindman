import Hindman168.NativeRationalDegreeOneWeightedInverse
import Hindman168.NativePolynomialVariableEquiv
import Hindman168.MvBinomialVariableEquiv

/-! GENUINE degree-one inverse for ANY actual finite variable type,
including Unit used by true polynomial recursion. Original cube discrepancy,
NONZERO character, finite grid and BOTH raw scalar coefficient bounds survive. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_one_finite_variables_inverse {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 1)
    (σ : Type*) [Fintype σ] (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial σ D.E,
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
        ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) 1 J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let e := Fintype.equivFin σ
  obtain ⟨M,hM,hInverse⟩ := native_rational_degree_one_weighted_canonical_inverse D L (Fintype.card σ) δ hδ
  refine ⟨M,hM,?_⟩
  intro p hp N hN H hH hLarge
  have hWeight := rough_vector_rename_weighted L.layer L.antitone e hp
  have hBad : δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin (Fintype.card σ)) N)
      (nativeMvPolynomialOrbit D (roughVectorMvRename e p)) H‖ := by
    rw [native_polynomial_variable_equiv_cube_discrepancy D e p N H]
    exact hLarge
  obtain ⟨χ,hχ,hNorm,hGrid,hCoeffs,hBinomial⟩ := hInverse _ hWeight N hN H hH hBad
  refine ⟨χ,hχ,hNorm,hGrid,?_,?_⟩
  · intro J hJ
    have hPos : 0 < ∑ i, scalarVariableAssignmentEquiv e ℕ J i := by
      simpa only [scalar_variable_equiv_sum] using hJ
    simpa only [rough_vector_rename_projection,scalar_variable_equiv_coefficient,scalar_variable_equiv_sum] using
      hCoeffs (scalarVariableAssignmentEquiv e ℕ J) hPos
  · intro J hJ
    have hPos : 0 < ∑ i, scalarVariableAssignmentEquiv e ℕ J i := by
      simpa only [scalar_variable_equiv_sum] using hJ
    simpa only [rough_vector_rename_projection,mv_binomial_variable_equiv_coefficient,scalar_variable_equiv_sum] using
      hBinomial (scalarVariableAssignmentEquiv e ℕ J) hPos

end Hindman168
