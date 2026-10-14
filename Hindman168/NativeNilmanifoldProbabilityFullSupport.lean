import Hindman168.NativeNilmanifoldQuotientProbability

/-! The actual normalized invariant probability is positive on every
nonempty open set of the original compact native coset space. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_quotient_probability_fullSupport {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.IsOpenPosMeasure (nativeNilmanifoldQuotientProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := native_nilmanifold_quotient_probability_isProbability D
  letI := native_nilmanifold_quotient_probability_invariant D
  refine ⟨fun U hU hne => ?_⟩
  exact (measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero D.G isCompact_univ
    (by rw [measure_univ]; exact one_ne_zero) hU hne).ne'

end Hindman168
