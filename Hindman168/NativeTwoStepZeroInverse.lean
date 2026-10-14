import Hindman168.NativeCentralZeroPolynomialDetection
import Hindman168.NativeAbelianCanonicalInverse

/-! GENUINE completed ZERO-FREQUENCY branch in step TWO: actual child
abelian inverse is proved, and its original horizontal obstruction is pulled
back. Nonzero-frequency branch and full nonabelian inverse remain open. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_two_step_zero_polynomial_inverse (D : NativeNilmanifoldData.{u} 2)
    (n d : ℕ) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
    letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : ℝ, 0 < A ∧ ∀ p : RoughVectorMvPolynomial (Fin n) D.E,
      RoughVectorMvDegreeLE p d → ∀ N : ℕ, 0 < N →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin n) N)
            (nativeMvPolynomialOrbit D p) (nativeCentralFourierProjection D 0 F)‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ A ∧
            (∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) d J : ℝ) : UnitAddCircle)‖ ≤ A := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
  letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_central_zero_polynomial_detection D η hη
  obtain ⟨M,hM,hInverse⟩ := native_abelian_canonical_polynomial_inverse (nativeCentralQuotientData D) n d θ hθ
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  refine ⟨nativeCentralCharacterBudget D (M : ℝ),
    hMReal.trans_le (native_central_character_budget_ge D (M : ℝ) hMReal.le), ?_⟩
  intro p hp N hN F hF hLarge
  obtain ⟨G,hG,hGD⟩ := hDetect p (scalarMvIntegerCube (Fin n) N) F hF hLarge
  obtain ⟨χ,hHor,hNorm,_,hCoeff,hBinomial⟩ := hInverse (nativeCentralPolynomialProjection D p)
    (native_central_polynomial_projection_degree D p d hp) N hN G (hP G hG) hGD.le
  refine ⟨nativeCentralCharacterPullback D χ,
    native_central_character_pullback_horizontal D χ hHor,
    native_central_character_pullback_bound D (M : ℝ) hMReal.le χ hNorm,
    native_central_character_pullback_grid D (M : ℝ) hMReal.le χ hNorm hHor, ?_, ?_⟩
  · intro J hJ
    rw [← native_central_polynomial_projection_scalar]
    exact (hCoeff J hJ).trans (native_central_character_budget_ge D (M : ℝ) hMReal.le)
  · intro J hJ
    rw [← native_central_polynomial_projection_scalar]
    exact (hBinomial J hJ).trans (native_central_character_budget_ge D (M : ℝ) hMReal.le)

end Hindman168
