import Hindman168.NativeAbelianCanonicalHaar
import Hindman168.NativeAbelianBinomialObstruction
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! Genuine ABELIAN root inverse with the ORIGINAL canonical Haar and
actual logarithmic-polynomial orbit, ordinary AND paper-binomial bounds. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_abelian_canonical_polynomial_inverse (D : NativeNilmanifoldData.{u} 1)
    (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial (Fin n) D.E,
      RoughVectorMvDegreeLE p d → ∀ N : ℕ, 0 < N →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin n) N)
            (nativeMvPolynomialOrbit D p) F‖ →
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
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  obtain ⟨M,hM,hInverse⟩ := native_abelian_binomial_observable_obstruction D n d δ hδ
  refine ⟨M,hM,?_⟩
  intro p hp N hN F hF hLarge
  let Q : (Fin n → ℝ) → D.G := fun x =>
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)
  have hQ : ∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (Q x) =
    roughVectorMvEval p x := fun x => nativeLieGlobalLogarithm_exponential (E := D.E) _
  apply hInverse Q p hp hQ N hN F hF
  rw [native_abelian_torus_haar_canonical_integral]
  exact hLarge

end Hindman168
