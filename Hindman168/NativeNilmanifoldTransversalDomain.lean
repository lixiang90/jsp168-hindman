import Hindman168.NativeNilmanifoldCountingRecovery

/-! The ACTUAL pointwise transversal is a genuine ORIGINAL Haar fundamental
domain, and its normalized quotient measure is ORIGINAL canonical probability. -/

namespace Hindman168
open Set MeasureTheory Measure
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_measurable_transversal_fundamental {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    IsFundamentalDomain D.Γ.op (nativeNilmanifoldMeasurableTransversal D) (nativeNilmanifoldGroupHaar D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  have h := native_nilmanifold_measurable_transversal_spec D
  exact IsFundamentalDomain.mk' h.1.nullMeasurableSet
    (coset_transversal_unique_op_translate D.Γ (nativeNilmanifoldMeasurableTransversal D) h.2.2.1 h.2.2.2)

theorem native_nilmanifold_transversal_canonical_probability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    fundamentalCosetProbability D.Γ (nativeNilmanifoldGroupHaar D) (nativeNilmanifoldMeasurableTransversal D) =
      nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI := native_nilmanifold_lattice_countable D
  letI := native_nilmanifold_group_haar_rightInvariant D
  exact fundamental_coset_probability_domain_independent D.Γ (nativeNilmanifoldGroupHaar D)
    (nativeNilmanifoldMeasurableTransversal D) (nativeNilmanifoldFundamentalDomain D)
    (native_nilmanifold_measurable_transversal_fundamental D)
    (native_nilmanifold_fundamental_domain_spec D).2.1

end Hindman168
