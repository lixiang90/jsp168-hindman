import Hindman168.NativeTerminalReducedPairRegularity
import Hindman168.NativeTerminalReducedPairDiscrepancy
import Hindman168.BoundedLipschitzNormalization

/-! ONE FIXED finite ACTUAL UNIT reduced observable family detects ALL
large SAME relative pair means, before original inputs/compact translations/samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_terminal_reduced_pair_unit_detection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0)
    (K : Set D.G) (hK : IsCompact K) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧
      ∃ P : Finset C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ),
        (∀ H ∈ P, H ∈ unitLipschitzObservables
          ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)) ∧
        ∀ {α : Type*} (a : Finset α)
          (f : α → (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ),
          ∀ g ∈ K, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
            η ≤ ‖finiteComplexSetMean a (fun x => nativeTerminalRelativePairObservable D d hd k g F (f x))‖ →
            ∃ H ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a
              (fun x => nativeRelativeReductionFactorMap D d hd (f x)) H‖ := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRelativeReducedData D d hd)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := native_terminal_reduced_pair_regular_approximation D d hd k K hK (η/8) (by positivity)
  let R : ℝ := 1+B+L
  have hR : 0 < R := by dsimp only [R]; linarith only [hB,hL]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hL]
  have hLR : L ≤ R := by dsimp only [R]; linarith only [hB]
  let scale : C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ) →
    C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ) := fun H => (R : ℂ)⁻¹ • H
  refine ⟨(η/2)/R,by positivity,P.image scale,?_,?_⟩
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hH
    exact bounded_lipschitz_normalization _ G B L R hR hBR hLR (hP G hG).1 (hP G hG).2
  · intro α a f g hg F hF hLarge
    obtain ⟨G,hG,hApprox⟩ := hClose g hg F hF
    rw [← native_terminal_reduced_pair_sample_discrepancy D d hd hdeg k hk g a f F] at hLarge
    let orbit := fun x => nativeRelativeReductionFactorMap D d hd (f x)
    have hDetect := linear_discrepancy_approximant_detection _
      (nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a orbit)
      (native_nilmanifold_finite_discrepancy_norm (nativeRelativeReducedData D d hd) a orbit)
      (nativeTerminalReducedMetricObservable D d hd k g F) G (η/8) η hApprox hLarge
    have hGD : η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a orbit G‖ := by
      linarith only [hη,hDetect]
    refine ⟨scale G,Finset.mem_image.mpr ⟨G,hG,rfl⟩,?_⟩
    change (η/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a orbit ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR,div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hGD (inv_pos.mpr hR)

end Hindman168
