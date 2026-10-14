import Hindman168.NativeRationalTerminalZeroUnitDetection
import Hindman168.NativeRationalTerminalPolynomial

/-! TRUE zero-mode NativeRationalTerminalZeroPolynomialDetection on ACTUAL original terminal quotient.
All canonical Haar, SAME image samples and specified-metric inputs are PROVED.
Finite families and positive bounds precede ALL original source observations. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_zero_polynomial_detection {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
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
    ∃ θ : ℝ, 0 < θ ∧
      ∃ P : Finset C((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ, ℂ),
        (∀ G ∈ P, G ∈ unitLipschitzObservables
          ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)) ∧
        ∀ {σ : Type*} (p : RoughVectorMvPolynomial σ D.E) (a : Finset (σ → ℤ))
          (F : C(D.G ⧸ D.Γ, ℂ)), F ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a (nativeMvPolynomialOrbit D p)
            (nativeRationalTerminalFourierProjection D L 0 F)‖ →
          ∃ G ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalTerminalQuotientData D L) a
            (nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D L) (nativeRationalTerminalPolynomial D L p)) G‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_rational_terminal_zero_unit_detection D L η hη
  refine ⟨θ,hθ,P,hP,?_⟩
  intro σ p a F hF hLarge
  obtain ⟨G,hG,hGD⟩ := hDetect a (nativeMvPolynomialOrbit D p) F hF hLarge
  refine ⟨G,hG,?_⟩
  have he : (fun x => nativeRationalTerminalFactorMap D L (nativeMvPolynomialOrbit D p x)) =
    nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D L) (nativeRationalTerminalPolynomial D L p) :=
      funext (native_rational_terminal_polynomial_integer_orbit D L p)
  rwa [he] at hGD

end Hindman168
