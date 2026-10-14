import Hindman168.NativeRationalDegreeOneProbability
import Hindman168.NativeAbelianCanonicalInverse

/-! TRUE degree-one filtration base case on the ORIGINAL native datum,
including an ACTUALLY NONZERO horizontal character, fixed finite grid,
operator norm and complete monomial/paper-binomial coefficient bounds. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_one_canonical_polynomial_inverse {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 1)
    (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial (Fin n) D.E,
      RoughVectorMvDegreeLE p d → ∀ N : ℕ, 0 < N →
        ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin n) N)
            (nativeMvPolynomialOrbit D p) H‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) d J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,hM,hInverse⟩ := native_abelian_canonical_polynomial_inverse (nativeRationalDegreeOneData D L) n d δ hδ
  refine ⟨M,hM,?_⟩
  intro p hp N hN H hH hLarge
  have hOrbit : nativeMvPolynomialOrbit (nativeRationalDegreeOneData D L) p = nativeMvPolynomialOrbit D p :=
    funext (native_rational_degree_one_original_polynomial_sample D L p)
  have hBad : δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeOneData D L)
      (scalarMvIntegerCube (Fin n) N) (nativeMvPolynomialOrbit (nativeRationalDegreeOneData D L) p) H‖ := by
    rw [hOrbit,native_rational_degree_one_original_finite_discrepancy]
    exact hLarge
  exact hInverse p hp N hN H hH hBad

end Hindman168
