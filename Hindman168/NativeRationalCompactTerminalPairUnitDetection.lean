import Hindman168.NativeRationalBasepointReducedPairRegularity
import Hindman168.NativeRationalCompactReducedPolynomialDiscrepancy
import Hindman168.BoundedLipschitzNormalization

/-! Fixed actual finite unit family detects every large original derivative mean on the actual weighted degree-reduced polynomial. Constants precede all raw coefficients and shifts. This is not a quantitative inverse. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_rational_compact_terminal_pair_unit_detection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (η : ℝ) (hη : 0 < η) :
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
        ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
          (h : ℤ) (a : Finset ℤ), ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          η ≤ ‖finiteComplexSetMean a (fun n =>
            nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
              star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n))))‖ →
          ∃ J ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a
            (fun n => nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D L)
              (nativeRationalCompactReducedPolynomial D L p hp h) (fun _ => n)) J‖ := by
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
  let K := nativeRationalRepresentativeSet D
  have hK : IsCompact K := native_rational_representative_set_compact D
  obtain ⟨B,C,hB,hC,P,hP,hClose⟩ := native_rational_basepoint_reduced_pair_regular_approximation
    D L k K K hK hK (η/8) (by positivity)
  let R : ℝ := 1+B+C
  have hR : 0 < R := by dsimp only [R]; linarith only [hB,hC]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hC]
  have hCR : C ≤ R := by dsimp only [R]; linarith only [hB]
  let scale : C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ) →
    C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ) := fun J => (R : ℂ)⁻¹ • J
  refine ⟨(η/2)/R,by positivity,P.image scale,?_,?_⟩
  · intro J hJ
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hJ
    exact bounded_lipschitz_normalization _ G B C R hR hBR hCR (hP G hG).1 (hP G hG).2
  · intro p hp h a H hH hLarge
    have hr : nativeRationalBasepointRepresentative D p ∈ K := native_rational_representative_mem D _
    have ht : nativeRationalShiftRepresentative D p h ∈ K := native_rational_representative_mem D _
    obtain ⟨G,hG,hApprox⟩ := hClose _ hr _ ht H hH
    rw [← native_rational_compact_reduced_polynomial_discrepancy D L hdeg p hp k hk h a H] at hLarge
    let orbit := fun n => nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D L)
      (nativeRationalCompactReducedPolynomial D L p hp h) (fun _ => n)
    have hDetect := linear_discrepancy_approximant_detection _
      (nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a orbit)
      (native_nilmanifold_finite_discrepancy_norm (nativeRationalDegreeReducedData D L) a orbit)
      (nativeRationalTerminalReducedPairObservable D L k (nativeRationalShiftRepresentative D p h)
        (nativeBasepointObservable D (nativeRationalBasepointRepresentative D p) H)) G (η/8) η hApprox hLarge
    have hGD : η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a orbit G‖ := by
      linarith only [hη,hDetect]
    refine ⟨scale G,Finset.mem_image.mpr ⟨G,hG,rfl⟩,?_⟩
    change (η/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a orbit ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR,div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hGD (inv_pos.mpr hR)

end Hindman168
