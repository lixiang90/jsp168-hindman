import Hindman168.NativeRelativeReductionProjection
import Hindman168.CentralSubgroupFactorProbability
import Hindman168.NativeNilmanifoldBorelProbability

/-! ACTUAL pushforward of ACTUAL original relative canonical Haar to
SAME terminal quotient preserves probability, invariance and integrals. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeRelativeReductionProbability {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    @Measure ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)
      (borel ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : BorelSpace ((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) :=
    native_nilmanifold_coset_borel (nativeRelativeSquareData D d hd 1)
  exact centralSubgroupFactorProbability (nativeRelativeTerminalSubgroup D d hd)
    (nativeRelativeSquareData D d hd 1).Γ (nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1))

theorem native_relative_reduction_probability_isProbability {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    IsProbabilityMeasure (nativeRelativeReductionProbability D d hd) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : BorelSpace ((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) :=
    native_nilmanifold_coset_borel (nativeRelativeSquareData D d hd 1)
  letI := native_nilmanifold_quotient_probability_isProbability (nativeRelativeSquareData D d hd 1)
  exact central_subgroup_factor_probability_isProbability (nativeRelativeTerminalSubgroup D d hd)
    (nativeRelativeSquareData D d hd 1).Γ (nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1))

theorem native_relative_reduction_probability_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    ∀ F : C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ),
      (∫ y, F y ∂nativeRelativeReductionProbability D d hd) =
      ∫ q, F (nativeRelativeReductionFactorMap D d hd q)
        ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : BorelSpace ((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) :=
    native_nilmanifold_coset_borel (nativeRelativeSquareData D d hd 1)
  intro F
  exact central_subgroup_factor_probability_integral (nativeRelativeTerminalSubgroup D d hd)
    (nativeRelativeSquareData D d hd 1).Γ (nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1)) F

theorem native_relative_reduction_probability_translate {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      borel ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)
    ∀ g : (nativeRelativeReducedData D d hd).G,
      Measure.map (fun q : (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ => g • q)
        (nativeRelativeReductionProbability D d hd) = nativeRelativeReductionProbability D d hd := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    borel ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ)
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : BorelSpace ((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) :=
    native_nilmanifold_coset_borel (nativeRelativeSquareData D d hd 1)
  intro g
  exact central_subgroup_factor_probability_translate (nativeRelativeTerminalSubgroup D d hd)
    (nativeRelativeSquareData D d hd 1).Γ (nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1))
    (native_nilmanifold_quotient_probability_translate (nativeRelativeSquareData D d hd 1)) g

end Hindman168
