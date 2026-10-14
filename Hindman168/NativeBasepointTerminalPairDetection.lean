import Hindman168.NativeBasepointReducedPairRegularity
import Hindman168.NativeBasepointTerminalPairSamples
import Hindman168.NativeTerminalReducedPairDiscrepancy
import Hindman168.BoundedLipschitzNormalization

/-! ONE FIXED original compact representative set and actual reduced UNIT
family detect ALL original univariate terminal derivative means, including
arbitrary original starting values and unbounded coefficients. Actual
original samples and SAME stretch d are retained. This is not an inverse. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_terminal_pair_uniform_detection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    ∃ K : Set D.G, IsCompact K ∧ ∃ θ : ℝ, 0 < θ ∧
      ∃ P : Finset C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ),
        (∀ H ∈ P, H ∈ unitLipschitzObservables
          ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)) ∧
        ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (h : ℤ),
          ∃ r ∈ K, ∃ γ0 : D.Γ,
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p 0) = r * γ0 ∧
          ∃ t ∈ K, ∃ γh : D.Γ,
            nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h = t * γh ∧
            ∀ (a : Finset ℤ), ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
              η ≤ ‖finiteComplexSetMean a (fun n => nativeOriginalTerminalFourierProjection D d hd k F
                (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
                star (nativeOriginalTerminalFourierProjection D d hd k F
                  (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ)))‖ →
              ∃ H ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a
                (fun n => nativeRelativeReductionFactorMap D d hd
                  (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
                    (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)) H‖ := by
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
  obtain ⟨K,hK,hRep⟩ := native_exists_compact_coset_representatives D
  obtain ⟨B,L,hB,hL,P,hP,hClose⟩ := native_basepoint_reduced_pair_regular_approximation D d hd k K K hK hK
    (η/8) (by positivity)
  let R : ℝ := 1+B+L
  have hR : 0 < R := by dsimp only [R]; linarith only [hB,hL]
  have hBR : B ≤ R := by dsimp only [R]; linarith only [hL]
  have hLR : L ≤ R := by dsimp only [R]; linarith only [hB]
  let scale : C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ) →
    C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ) := fun H => (R : ℂ)⁻¹ • H
  refine ⟨K,hK,(η/2)/R,by positivity,P.image scale,?_,?_⟩
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hH
    exact bounded_lipschitz_normalization _ G B L R hR hBR hLR (hP G hG).1 (hP G hG).2
  · intro p hp h
    obtain ⟨r,hr,γ0,hγ0⟩ := hRep
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p 0))
    obtain ⟨t,ht,γh,hγh⟩ := hRep (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h)
    refine ⟨r,hr,γ0,hγ0,t,ht,γh,hγh,?_⟩
    intro a F hF hLarge
    let f : ℤ → (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ :=
      fun n => (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
        (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)
    let orbit := fun n => nativeRelativeReductionFactorMap D d hd (f n)
    have hPair : η ≤ ‖finiteComplexSetMean a
        (fun n => nativeTerminalRelativePairObservable D d hd k t (nativeBasepointObservable D r F) (f n))‖ := by
      change η ≤ ‖finiteComplexSetMean a (fun n => nativeTerminalRelativePairObservable D d hd k t
        (nativeBasepointObservable D r F) (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ))‖
      rw [native_basepoint_terminal_pair_original_mean D d hd p hp r t γ0 γh hγ0 k h a hγh]
      exact hLarge
    rw [← native_terminal_reduced_pair_sample_discrepancy D d hd hdeg k hk t a f
      (nativeBasepointObservable D r F)] at hPair
    obtain ⟨G,hG,hApprox⟩ := hClose r hr t ht F hF
    have hDetect := linear_discrepancy_approximant_detection _
      (nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a orbit)
      (native_nilmanifold_finite_discrepancy_norm (nativeRelativeReducedData D d hd) a orbit)
      (nativeTerminalReducedMetricObservable D d hd k t (nativeBasepointObservable D r F)) G (η/8) η hApprox hPair
    have hGD : η/2 < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a orbit G‖ := by
      linarith only [hη,hDetect]
    refine ⟨scale G,Finset.mem_image.mpr ⟨G,hG,rfl⟩,?_⟩
    change (η/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a orbit ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR,div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hGD (inv_pos.mpr hR)

end Hindman168
