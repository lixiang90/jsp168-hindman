import Hindman168.NativeCentralChildDiscrepancy
import Hindman168.LinearDiscrepancyStability

/-! One finite bounded spatial-Lipschitz CHILD family detects EVERY parent
zero-mode discrepancy, with the SAME actual projected samples and child Haar. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_child_regular_detection {s : ℕ} (D : NativeNilmanifoldData.{u} s)
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
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
      ∃ P : Finset C((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ, ℂ),
        (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal L) G) ∧
        ∀ {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ)
          (F : C(D.G ⧸ D.Γ, ℂ)), F ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f (nativeCentralFourierProjection D 0 F)‖ →
          ∃ G ∈ P, η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeCentralQuotientData D) a
            (fun x => centralFactorCosetMap D.Γ (f x)) G‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralQuotientData D).E := borel (nativeCentralQuotientData D).E
  letI : MeasurableSpace (nativeCentralQuotientData D).G := borel (nativeCentralQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := native_central_child_zero_regular_approximation D (η/8) (by positivity)
  refine ⟨B,L,hB,hL,P,hP,?_⟩
  intro α a f F hF hLarge
  obtain ⟨G,hG,hApprox⟩ := hClose F hF
  refine ⟨G,hG,?_⟩
  rw [native_central_child_zero_discrepancy] at hLarge
  have hDetect := linear_discrepancy_approximant_detection _
    (nativeNilmanifoldFiniteDiscrepancy (nativeCentralQuotientData D) a
      (fun x => centralFactorCosetMap D.Γ (f x)))
    (native_nilmanifold_finite_discrepancy_norm (nativeCentralQuotientData D) a _)
    (nativeCentralChildZeroObservable D F) G (η/8) η hApprox hLarge
  linarith only [hη,hDetect]

end Hindman168
