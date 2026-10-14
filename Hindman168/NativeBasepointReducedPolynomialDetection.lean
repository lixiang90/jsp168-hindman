import Hindman168.NativeBasepointReducedPolynomial
import Hindman168.NativeBasepointTerminalPairDetection

/-! ONE FIXED actual reduced UNIT family detects original terminal derivative
means on the ACTUAL constructed reduced polynomial orbit. All actual relative
coefficient membership/orbit compatibility inputs are discharged. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_reduced_polynomial_uniform_detection {s : ℕ}
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
                (fun n => nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
                  (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n)) H‖ := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨K,hK,θ,hθ,P,hP,hDetect⟩ := native_basepoint_terminal_pair_uniform_detection D d hd hdeg k hk η hη
  refine ⟨K,hK,θ,hθ,P,hP,?_⟩
  intro p hp h
  obtain ⟨r,hr,γ0,hγ0,t,ht,γh,hγh,hOrig⟩ := hDetect p hp h
  refine ⟨r,hr,γ0,hγ0,t,ht,γh,hγh,?_⟩
  intro a F hF hLarge
  obtain ⟨H,hH,hδ⟩ := hOrig a F hF hLarge
  refine ⟨H,hH,?_⟩
  have he : (fun n : ℤ => nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n)) =
      (fun n => nativeRelativeReductionFactorMap D d hd
        (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)) := by
    funext n
    exact native_basepoint_reduced_polynomial_orbit D d hd p hp r t h n
  rw [he]
  exact hδ

end Hindman168
