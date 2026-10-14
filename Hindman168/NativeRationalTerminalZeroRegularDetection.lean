import Hindman168.NativeRationalTerminalZeroRegularFamily
import Hindman168.NativeRationalTerminalZeroDiscrepancy
import Hindman168.LinearDiscrepancyStability

/-! TRUE zero-mode NativeRationalTerminalZeroRegularDetection on ACTUAL original terminal quotient.
All canonical Haar, SAME image samples and specified-metric inputs are PROVED.
Finite families and positive bounds precede ALL original source observations. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_zero_regular_detection {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
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
    ∃ B B_L : ℝ, 0 < B ∧ 0 < B_L ∧
      ∃ P : Finset C((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ, ℂ),
        (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal B_L) G) ∧
        ∀ {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ)
          (F : C(D.G ⧸ D.Γ, ℂ)), F ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f (nativeRationalTerminalFourierProjection D L 0 F)‖ →
          ∃ G ∈ P, η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalTerminalQuotientData D L) a
            (fun x => nativeRationalTerminalFactorMap D L (f x)) G‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
  obtain ⟨B,B_L,hB,hL,P,hP,hClose⟩ := native_rational_terminal_zero_regular_approximation D L (η/8) (by positivity)
  refine ⟨B,B_L,hB,hL,P,hP,?_⟩
  intro α a f F hF hLarge
  obtain ⟨G,hG,hApprox⟩ := hClose F hF
  refine ⟨G,hG,?_⟩
  rw [native_rational_terminal_zero_discrepancy] at hLarge
  have hDetect := linear_discrepancy_approximant_detection _
    (nativeNilmanifoldFiniteDiscrepancy (nativeRationalTerminalQuotientData D L) a
      (fun x => nativeRationalTerminalFactorMap D L (f x)))
    (native_nilmanifold_finite_discrepancy_norm (nativeRationalTerminalQuotientData D L) a _)
    (nativeRationalTerminalZeroObservable D L F) G (η/8) η hApprox hLarge
  linarith only [hη,hDetect]

end Hindman168
