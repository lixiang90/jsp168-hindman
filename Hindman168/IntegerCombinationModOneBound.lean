import Hindman168.RoughExactInterpolationModOne

namespace Hindman168
open scoped BigOperators Classical

theorem integer_combination_mod_one_bound {α : Type*} [Fintype α]
    (m : α → ℤ) (v : α → ℝ) (eps : ℝ)
    (hv : ∀ x, ‖(v x : UnitAddCircle)‖ ≤ eps) :
    ‖((∑ x, (m x : ℝ)*v x : ℝ) : UnitAddCircle)‖ ≤ (∑ x, (m x).natAbs : ℕ)*eps := by
  have hex : ∀ x, ∃ b : ℤ, |v x-(b : ℝ)| ≤ eps :=
    fun x => (rough_mod_one_near_integer_iff (v x) eps).mp (hv x)
  choose b hb using hex
  apply (rough_mod_one_near_integer_iff _ _).mpr
  refine ⟨∑ x, m x*b x, ?_⟩
  have he : (∑ x, (m x : ℝ)*v x)-((∑ x, m x*b x : ℤ) : ℝ) =
      ∑ x, (m x : ℝ)*(v x-(b x : ℝ)) := by
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ x, |(m x : ℝ)*(v x-(b x : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ((m x).natAbs : ℝ)*eps := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      simpa only [Nat.cast_natAbs, Int.cast_abs] using
        mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (m x : ℝ))
    _ = _ := by rw [← Finset.sum_mul, Nat.cast_sum]

end Hindman168
