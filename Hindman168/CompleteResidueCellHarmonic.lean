import Hindman168.CompleteResidueCell

namespace Hindman168
open scoped BigOperators

theorem completeResidueCell_sum (k : ℤ) (M q : ℕ) (hM : 0 < M)
    (r : Fin M) (F : ℤ → ℝ) :
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, F y) =
      ∑ t : Fin q, F (completeResidueCellPoint k M q r t) := by
  symm
  apply Finset.sum_bij (fun t _ => completeResidueCellPoint k M q r t)
  · exact fun t _ => completeResidueCellPoint_mem k M q hM r t
  · exact fun t _ u _ htu => completeResidueCellPoint_injective k M q hM r htu
  · intro y hy
    obtain ⟨t, ht⟩ := completeResidueCellPoint_surjective k M q hM r y hy
    exact ⟨t, Finset.mem_univ _, ht⟩
  · intro t _
    rfl

theorem completeResidueCell_harmonic_error (k : ℤ) (M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (r : Fin M) (F : ℤ → ℝ) (hF : ∀ y, |F y| ≤ 1)
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) :
    |(∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, (1 / (y : ℝ)) * F y) /
      (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, 1 / (y : ℝ)) -
        finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t))| ≤
          (M * q : ℕ) / ((k : ℝ) * (M * q : ℕ)) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  rw [completeResidueCell_sum k M q hM, completeResidueCell_sum k M q hM]
  apply harmonicCell_conditional_expectation_error
    (fun t : Fin q => (completeResidueCellPoint k M q r t : ℝ))
    (fun t => F (completeResidueCellPoint k M q r t)) _ _ hA (Nat.cast_nonneg _)
  · intro t
    obtain ⟨hlo, hhi⟩ := completeResidueCellPoint_bounds k M q hM r t
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi.le
  · exact fun t => hF _

end Hindman168
