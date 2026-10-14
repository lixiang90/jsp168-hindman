import Hindman168.NativeCentralChildUnitDetection
import Hindman168.NativeCentralPolynomialProjection

/-! Actual zero-mode detection on the genuine projected logarithmic
polynomial orbit. Constants and unit list precede ALL polynomials/samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_zero_polynomial_detection {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
    letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧
      ∃ P : Finset C((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ, ℂ),
        (∀ G ∈ P, G ∈ unitLipschitzObservables
          ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ)) ∧
        ∀ {σ : Type*} (p : RoughVectorMvPolynomial σ D.E) (a : Finset (σ → ℤ))
          (F : C(D.G ⧸ D.Γ, ℂ)), F ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a (nativeMvPolynomialOrbit D p)
            (nativeCentralFourierProjection D 0 F)‖ →
          ∃ G ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeCentralQuotientData D) a
            (nativeMvPolynomialOrbit (nativeCentralQuotientData D) (nativeCentralPolynomialProjection D p)) G‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
  letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_central_child_unit_detection D η hη
  refine ⟨θ,hθ,P,hP,?_⟩
  intro σ p a F hF hLarge
  obtain ⟨G,hG,hGD⟩ := hDetect a (nativeMvPolynomialOrbit D p) F hF hLarge
  refine ⟨G,hG,?_⟩
  have he : (fun x => centralFactorCosetMap D.Γ (nativeMvPolynomialOrbit D p x)) =
    nativeMvPolynomialOrbit (nativeCentralQuotientData D) (nativeCentralPolynomialProjection D p) :=
      funext (native_central_polynomial_projection_orbit D p)
  rwa [he] at hGD

end Hindman168
