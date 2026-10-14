import Hindman168.NativeNormalizedTerminalPairSampling
import Hindman168.NativeCompactCosetRepresentatives
import Hindman168.NativeTerminalReducedPairUnitDetection

/-! ONE FIXED compact representative set and finite ACTUAL reduced UNIT
family detect derivative means of ALL starting-zero original logarithmic
polynomials. The original coefficients are unbounded. Group membership and
samples are proved; full relative polynomial degree is not asserted here. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_normalized_terminal_pair_uniform_detection {s : ℕ}
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
        ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
          (h0 : roughVectorMvEval p (fun _ => 0) = 0) (h : ℤ),
          ∃ r ∈ K, ∃ γ : D.Γ, nativeIntegerLogPolynomialSequence D p 1 ^ h = r * γ ∧
            ∀ (a : Finset ℤ), ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
              η ≤ ‖finiteComplexSetMean a (fun n => nativeOriginalTerminalFourierProjection D d hd k F
                (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
                star (nativeOriginalTerminalFourierProjection D d hd k F
                  (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ)))‖ →
              ∃ H ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a
                (fun n => nativeRelativeReductionFactorMap D d hd
                  (nativeNormalizedIntegerPolynomialPair D d hd p hp h0 r h n :
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
  obtain ⟨K,hK,hRep⟩ := native_exists_compact_coset_representatives D
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_terminal_reduced_pair_unit_detection D d hd hdeg k hk K hK η hη
  refine ⟨K,hK,θ,hθ,P,hP,?_⟩
  intro p hp h0 h
  obtain ⟨r,hr,γ,hγ⟩ := hRep (nativeIntegerLogPolynomialSequence D p 1 ^ h)
  refine ⟨r,hr,γ,hγ,?_⟩
  intro a F hF hLarge
  let f : ℤ → (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ :=
    fun n => (nativeNormalizedIntegerPolynomialPair D d hd p hp h0 r h n :
      (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)
  apply hDetect a f r hr F hF
  change η ≤ ‖finiteComplexSetMean a (fun n => nativeTerminalRelativePairObservable D d hd k r F
    (nativeNormalizedIntegerPolynomialPair D d hd p hp h0 r h n :
      (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ))‖
  rw [native_normalized_terminal_pair_original_mean D d hd p hp h0 k r h a γ hγ]
  exact hLarge

end Hindman168
