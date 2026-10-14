import Hindman168.NativeDiagonalPairMetricDiscrepancy
import Hindman168.NativeDiagonalPairRegularFamily
import Hindman168.BoundedLipschitzNormalization

/-! ONE FIXED finite ACTUAL UNIT diagonal observable list detects EVERY
large ORIGINAL nonzero-frequency derivative on SAME projected polynomial
samples and genuine canonical Haar, before coefficients/shifts/sample sets. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_diagonal_pair_unit_detection {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : MeasurableSpace (nativeDiagonalQuotientData D).E := borel (nativeDiagonalQuotientData D).E
    letI : MeasurableSpace (nativeDiagonalQuotientData D).G := borel (nativeDiagonalQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeDiagonalQuotientData D).metric
    letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    ∃ θ : ℝ, 0 < θ ∧
      ∃ P : Finset C((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ, ℂ),
        (∀ G ∈ P, G ∈ unitLipschitzObservables
          ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ)) ∧
        ∀ {σ : Type*} (p : RoughVectorMvPolynomial σ D.E) (h : σ → ℤ)
          (a : Finset (σ → ℤ)) (F : C(D.G ⧸ D.Γ, ℂ)),
          F ∈ unitLipschitzObservables (D.G ⧸ D.Γ) →
          η ≤ ‖finiteComplexSetMean a (fun x => nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p (x+h)) *
            star (nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p x)))‖ →
          ∃ G ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeDiagonalQuotientData D) a
            (nativeMvPolynomialOrbit (nativeDiagonalQuotientData D)
              (nativeDiagonalPolynomialProjection D (nativePairShiftPolynomial D p h))) G‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : MeasurableSpace (nativeDiagonalQuotientData D).E := borel (nativeDiagonalQuotientData D).E
  letI : MeasurableSpace (nativeDiagonalQuotientData D).G := borel (nativeDiagonalQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeDiagonalQuotientData D).metric
  letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeDiagonalQuotientData D)
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := native_diagonal_pair_regular_approximation D k (η/8) (by positivity)
  let R : ℝ := 1+B+L
  have hR : 0 < R := by dsimp only [R]; linarith only [hB,hL]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hL]
  have hLR : L ≤ R := by dsimp only [R]; linarith only [hB]
  let scale : C((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ, ℂ) →
    C((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ, ℂ) := fun G => (R : ℂ)⁻¹ • G
  refine ⟨(η/2)/R,by positivity,P.image scale,?_,?_⟩
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hH
    exact bounded_lipschitz_normalization _ G B L R hR hBR hLR (hP G hG).1 (hP G hG).2
  · intro σ p h a F hF hLarge
    obtain ⟨G,hG,hApprox⟩ := hClose F hF
    rw [← native_diagonal_pair_metric_polynomial_discrepancy D p h a k hk F] at hLarge
    let orbit := nativeMvPolynomialOrbit (nativeDiagonalQuotientData D)
      (nativeDiagonalPolynomialProjection D (nativePairShiftPolynomial D p h))
    have hDetect := linear_discrepancy_approximant_detection _
      (nativeNilmanifoldFiniteDiscrepancy (nativeDiagonalQuotientData D) a orbit)
      (native_nilmanifold_finite_discrepancy_norm (nativeDiagonalQuotientData D) a orbit)
      (nativeDiagonalPairMetricObservable D k F) G (η/8) η hApprox hLarge
    have hGD : η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeDiagonalQuotientData D) a orbit G‖ := by
      linarith only [hη,hDetect]
    refine ⟨scale G,Finset.mem_image.mpr ⟨G,hG,rfl⟩,?_⟩
    change (η/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy (nativeDiagonalQuotientData D) a orbit ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR,div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hGD (inv_pos.mpr hR)

end Hindman168
