import Hindman168.NativeRationalTerminalReducedPairRegularity
import Hindman168.NativeRationalTerminalReducedPairDiscrepancy
import Hindman168.BoundedLipschitzNormalization

/-! ONE FIXED finite ACTUAL UNIT reduced observable family detects ALL
large SAME relative pair means, before original inputs/compact translations/samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_rational_terminal_reduced_pair_unit_detection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (K : Set D.G) (hK : IsCompact K) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧
      ∃ P : Finset C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ),
        (∀ H ∈ P, H ∈ unitLipschitzObservables
          ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ)) ∧
        ∀ {α : Type*} (a : Finset α)
          (f : α → (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
          ∀ g ∈ K, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
            η ≤ ‖finiteComplexSetMean a (fun x => nativeRationalTerminalRelativePairObservable D L k g F (f x))‖ →
            ∃ H ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a
              (fun x => nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) (f x)) H‖ := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  obtain ⟨B,C,hB,hC,P,hP,hClose⟩ := native_rational_terminal_reduced_pair_regular_approximation D L k K hK (η/8) (by positivity)
  let R : ℝ := 1+B+C
  have hR : 0 < R := by dsimp only [R]; linarith only [hB,hC]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hC]
  have hLR : C ≤ R := by dsimp only [R]; linarith only [hB]
  let scale : C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ) →
    C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ) := fun H => (R : ℂ)⁻¹ • H
  refine ⟨(η/2)/R,by positivity,P.image scale,?_,?_⟩
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hH
    exact bounded_lipschitz_normalization _ G B C R hR hBR hLR (hP G hG).1 (hP G hG).2
  · intro α a f g hg F hF hLarge
    obtain ⟨G,hG,hApprox⟩ := hClose g hg F hF
    rw [← native_rational_terminal_reduced_pair_sample_discrepancy D L hdeg k hk g a f F] at hLarge
    let orbit := fun x => nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) (f x)
    have hDetect := linear_discrepancy_approximant_detection _
      (nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a orbit)
      (native_nilmanifold_finite_discrepancy_norm (nativeRationalDegreeReducedData D L) a orbit)
      (nativeRationalTerminalReducedPairObservable D L k g F) G (η/8) η hApprox hLarge
    have hGD : η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a orbit G‖ := by
      linarith only [hη,hDetect]
    refine ⟨scale G,Finset.mem_image.mpr ⟨G,hG,rfl⟩,?_⟩
    change (η/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a orbit ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR,div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hGD (inv_pos.mpr hR)

end Hindman168
