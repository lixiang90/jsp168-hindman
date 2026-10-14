import Hindman168.NativeRationalTerminalZeroPolynomialDetection
import Hindman168.RoughVectorZeroTrimProjection

/-! Actual zero-mode inverse reduction on TRUE weighted original polynomials:
same native image lattice/canonical Haar/unit family, actual output weights
and ordinary degree ell-1, with COMPLETE original scalar coefficient pullback. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_zero_weighted_polynomial_detection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧ ∃ P : Finset C((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ,ℂ),
      (∀ G ∈ P, G ∈ unitLipschitzObservables ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)) ∧
      ∀ {σ : Type*} (p : RoughVectorMvPolynomial σ D.E), RoughVectorMvWeightedDegree L.layer p 0 →
        ∀ (a : Finset (σ → ℤ)) (H : C(D.G ⧸ D.Γ,ℂ)), H ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a (nativeMvPolynomialOrbit D p)
            (nativeRationalTerminalFourierProjection D L 0 H)‖ →
          ∃ G ∈ P,
            RoughVectorMvWeightedDegree (nativeTerminalRationalLieFiltration D L).layer
              (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p)) 0 ∧
            RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p)) (ℓ-1) ∧
            θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalTerminalQuotientData D L) a
              (nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D L)
                (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p))) G‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_rational_terminal_zero_polynomial_detection D L η hη
  refine ⟨θ,hθ,P,hP,?_⟩
  intro σ p hp a H hH hLarge
  obtain ⟨G,hG,hBad⟩ := hDetect p a H hH hLarge
  refine ⟨G,hG,rough_vector_zero_trim_weighted _ (native_rational_terminal_polynomial_weighted D L hp),
    native_rational_terminal_polynomial_zero_trim_degree D L hp,?_⟩
  have he : nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D L)
      (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p)) =
      nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D L) (nativeRationalTerminalPolynomial D L p) := by
    funext x
    unfold nativeMvPolynomialOrbit
    rw [rough_vector_zero_trim_eval]
  rw [he]
  exact hBad

theorem native_rational_terminal_zero_trim_complete_scalar {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (χ : (nativeRationalTerminalQuotientData D L).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection χ (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p)) =
      roughVectorMvProjection (χ.comp (nativeRationalTerminalModelProjection D L).toLinearMap) p :=
  (rough_vector_zero_trim_projection χ _).trans (native_rational_terminal_polynomial_scalar D L p χ)

end Hindman168
