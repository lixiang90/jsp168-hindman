import Hindman168.NativeRelativeReductionProbability

/-! ACTUAL relative canonical Haar pushforward equals ACTUAL reduced
native canonical Haar, by genuinely proved original NONNORMAL uniqueness. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_relative_reduction_canonical_probability {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    nativeRelativeReductionProbability D d hd = nativeNilmanifoldBorelProbability (nativeRelativeReducedData D d hd) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  exact native_nilmanifold_borel_probability_unique (nativeRelativeReducedData D d hd)
    (nativeRelativeReductionProbability D d hd) (native_relative_reduction_probability_isProbability D d hd)
    (native_relative_reduction_probability_translate D d hd)

theorem native_relative_reduction_canonical_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    ∀ F : C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ),
      (∫ y, F y ∂nativeNilmanifoldQuotientProbability (nativeRelativeReducedData D d hd)) =
      ∫ q, F (nativeRelativeReductionFactorMap D d hd q)
        ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  intro F
  have hm := native_relative_reduction_probability_integral D d hd F
  rw [native_relative_reduction_canonical_probability D d hd] at hm
  exact (native_nilmanifold_borel_probability_integral (nativeRelativeReducedData D d hd)
    (fun y => F y)).symm.trans hm

end Hindman168
