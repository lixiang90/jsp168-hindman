import Hindman168.RoughHorizontalError

namespace Hindman168
open scoped BigOperators

theorem rough_mod_one_integer_combination {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (u : ι → ℝ) :
    ‖((∑ i ∈ s, (c i : ℝ)*u i : ℝ) : UnitAddCircle)‖ ≤
      ∑ i ∈ s, |(c i : ℝ)| * ‖(u i : UnitAddCircle)‖ := by
  apply (rough_mod_one_near_integer_iff _ _).mpr
  refine ⟨∑ i ∈ s, c i*round (u i), ?_⟩
  rw [Int.cast_sum]
  simp only [Int.cast_mul, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i ∈ s, |(c i : ℝ)*(u i-(round (u i) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, UnitAddCircle.norm_eq]

end Hindman168
