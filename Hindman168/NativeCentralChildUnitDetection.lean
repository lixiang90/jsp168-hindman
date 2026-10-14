import Hindman168.NativeCentralChildRegularDetection
import Hindman168.BoundedLipschitzNormalization

/-! Actual fixed finite UNIT child family and a positive fixed discrepancy
threshold, uniformly before all original samples and unit observables. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_central_child_unit_detection {s : ℕ} (D : NativeNilmanifoldData.{u} s)
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
        ∀ {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ)
          (F : C(D.G ⧸ D.Γ, ℂ)), F ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f (nativeCentralFourierProjection D 0 F)‖ →
          ∃ G ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeCentralQuotientData D) a
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
  obtain ⟨B,L,hB,hL,P,hP,hDetect⟩ := native_central_child_regular_detection D η hη
  let R : ℝ := 1+B+L
  have hR : 0 < R := by dsimp only [R]; linarith only [hB,hL]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hL]
  have hLR : L ≤ R := by dsimp only [R]; linarith only [hB]
  let scale : C((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ, ℂ) →
    C((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ, ℂ) := fun G => (R : ℂ)⁻¹ • G
  refine ⟨(η/2)/R, by positivity, P.image scale, ?_, ?_⟩
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hH
    exact bounded_lipschitz_normalization _ G B L R hR hBR hLR (hP G hG).1 (hP G hG).2
  · intro α a f F hF hLarge
    obtain ⟨G,hG,hGD⟩ := hDetect a f F hF hLarge
    refine ⟨scale G, Finset.mem_image.mpr ⟨G,hG,rfl⟩, ?_⟩
    change (η/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy (nativeCentralQuotientData D) a
      (fun x => centralFactorCosetMap D.Γ (f x)) ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR, div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hGD (inv_pos.mpr hR)

end Hindman168
