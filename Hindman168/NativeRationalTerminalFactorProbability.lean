import Hindman168.NativeRationalTerminalFactorTopology
import Hindman168.NativeNilmanifoldBorelProbability

/-! Actual original terminal factor pushforward equals the ACTUAL native
quotient canonical Haar by PROVED probability/invariance and genuine uniqueness. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalTerminalFactorProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    @Measure ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
      (borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
  exact Measure.map (nativeRationalTerminalFactorMap D L) (nativeNilmanifoldQuotientProbability D)

theorem native_rational_terminal_factor_probability_isProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    IsProbabilityMeasure (nativeRationalTerminalFactorProbability D L) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
  letI : BorelSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) := ⟨rfl⟩
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI := native_nilmanifold_quotient_probability_isProbability D
  exact Measure.isProbabilityMeasure_map
    (native_rational_terminal_factor_original_metric_openQuotient D L).continuous.measurable.aemeasurable

theorem native_rational_terminal_factor_probability_translate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (g : (nativeRationalTerminalQuotientData D L).G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
    Measure.map (fun y => g • y) (nativeRationalTerminalFactorProbability D L) = nativeRationalTerminalFactorProbability D L := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI := native_rational_terminal_subgroup_normal D L
  exact central_subgroup_factor_probability_translate (nativeRationalTerminalSubgroup D L) D.Γ
    (nativeNilmanifoldQuotientProbability D) (by
      intro h
      letI := native_nilmanifold_quotient_probability_invariant D
      exact measurePreserving_smul h _ |>.map_eq) g

theorem native_rational_terminal_factor_canonical_probability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    nativeRationalTerminalFactorProbability D L = nativeNilmanifoldBorelProbability (nativeRationalTerminalQuotientData D L) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  exact native_nilmanifold_borel_probability_unique (nativeRationalTerminalQuotientData D L)
    (nativeRationalTerminalFactorProbability D L) (native_rational_terminal_factor_probability_isProbability D L)
    (native_rational_terminal_factor_probability_translate D L)

end Hindman168
