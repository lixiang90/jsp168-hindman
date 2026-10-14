import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-! One GENUINE positive threshold works for every member of an actual
finite nonempty family; minimum is selected before all later sample data. -/
namespace Hindman168
open scoped Classical

theorem finite_positive_threshold_minimum {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ a i := by
  refine ⟨Finset.univ.inf' Finset.univ_nonempty a,?_,?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun i _hi => ha i)
  · intro i
    exact Finset.inf'_le a (Finset.mem_univ i)

end Hindman168
