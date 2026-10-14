import Hindman168.NativeRationalDegreeOneCanonicalInverse
import Hindman168.RoughVectorZeroTrimProjection

/-! The ACTUAL weighted degree-one base case uses raw ORIGINAL coefficient
polynomials, including high-degree zero-vector terms. A NONZERO character
and BOTH coefficient bounds apply to original scalar coefficients. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_one_weighted_polynomial_degree {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 1)
    {p : RoughVectorMvPolynomial σ D.E} (hp : RoughVectorMvWeightedDegree L.layer p 0) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim p) 1 :=
  rough_vector_zero_trim_degree L.layer L.antitone hp L.terminal

theorem native_rational_degree_one_zero_trim_orbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) :
    nativeMvPolynomialOrbit D (roughVectorMvZeroTrim p) x = nativeMvPolynomialOrbit D p x := by
  unfold nativeMvPolynomialOrbit
  rw [rough_vector_zero_trim_eval]

theorem native_rational_degree_one_weighted_canonical_inverse {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 1)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial (Fin n) D.E,
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
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
                (roughVectorMvProjection χ.toLinearMap p) 1 J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,hM,hInverse⟩ := native_rational_degree_one_canonical_polynomial_inverse D L n 1 δ hδ
  refine ⟨M,hM,?_⟩
  intro p hp N hN H hH hLarge
  have hDegree := native_rational_degree_one_weighted_polynomial_degree D L hp
  have hOrbit : nativeMvPolynomialOrbit D (roughVectorMvZeroTrim p) = nativeMvPolynomialOrbit D p :=
    funext (native_rational_degree_one_zero_trim_orbit D p)
  have hBad : δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin n) N)
      (nativeMvPolynomialOrbit D (roughVectorMvZeroTrim p)) H‖ := by
    rw [hOrbit]
    exact hLarge
  obtain ⟨χ,hχ,hNorm,hGrid,hCoeffs,hBinomial⟩ := hInverse _ hDegree N hN H hH hBad
  refine ⟨χ,hχ,hNorm,hGrid,?_,?_⟩
  · simpa only [rough_vector_zero_trim_projection] using hCoeffs
  · simpa only [rough_vector_zero_trim_projection] using hBinomial

end Hindman168
