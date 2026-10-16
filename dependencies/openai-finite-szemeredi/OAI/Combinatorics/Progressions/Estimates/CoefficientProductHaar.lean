/- Lean 4.32.2 / mathlib 905b958 elaboration compatibility (prepared_uncompiled).
Original Apache-2.0 source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CoefficientProductHaar.lean
Change: locally raise synthInstance.maxHeartbeats to 200000 for coefficientCoordinateTorus_measurePreserving.
The public declaration and its complete mathematical proof are unchanged.
No Lean, Lake, or cache invocation was performed for this text preparation. -/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

set_option synthInstance.maxHeartbeats 200000 in
theorem coefficientCoordinateTorus_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)] :
    MeasurePreserving (coefficientCoordinateTorus U) μ (Measure.pi ν) := by
  let _ := coefficientCoordinateTori_compact (K := K) U
  let _ : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let _ : (Measure.pi ν).IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := Measure.pi ν) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving (coefficientCoordinateTorus_continuous U)
    (coefficientCoordinateTorus_surjective U) (by simp)

end Erdos3.VectorPolynomial

end

end OAI
