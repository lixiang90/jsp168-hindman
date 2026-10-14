import Hindman168.UnitCircleDenseBumpDiscrepancy

namespace Hindman168
open scoped BigOperators Classical

/-- A genuine coarse inverse from actual dense modular interval visits. The
bound is uniform in eps, slope, offset and N, and is chosen from delta alone. -/
theorem unit_circle_dense_linear_coarse_inverse (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ (x b : ℝ) (N : ℕ), 0 < N → ∀ eps : ℝ, eps ≤ δ/10 →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n =>
        ‖(((b+(n : ℝ)*x : ℝ) : UnitAddCircle))‖ ≤ eps)).card →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ (N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ A := by
  obtain ⟨A, hA, hinv⟩ := unit_circle_affine_linear_inverse (δ^2/64) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro x b N hN eps heps hdense
  obtain ⟨k, hk, hkA, hnorm⟩ := hinv x b N hN (unitCircleComplexNormBump (δ/4))
    (unit_circle_norm_bump_unit_observable (δ/4) (by positivity) (by linarith))
    (unit_circle_dense_norm_bump_discrepancy δ hδ hδ1 x b N hN eps heps hdense)
  have heq : ‖(((k.natAbs : ℝ)*x : ℝ) : UnitAddCircle)‖ =
      ‖(((k : ℝ)*x : ℝ) : UnitAddCircle)‖ := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    by_cases h : (0 : ℝ) ≤ k
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), neg_mul, AddCircle.coe_neg, norm_neg]
  exact ⟨k.natAbs, hk, hkA, by simpa only [heq] using hnorm⟩

end Hindman168
