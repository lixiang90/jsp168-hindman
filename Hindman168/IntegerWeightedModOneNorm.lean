import Hindman168.RoughExactInterpolationModOne

namespace Hindman168
open scoped BigOperators Classical

theorem integer_weighted_mod_one_norm_bound {α : Type*} (s : Finset α)
    (m : α → ℤ) (v : α → ℝ) :
    ‖((∑ j ∈ s, (m j : ℝ)*v j : ℝ) : UnitAddCircle)‖ ≤
      ∑ j ∈ s, |(m j : ℝ)| * ‖(v j : UnitAddCircle)‖ := by
  apply (rough_mod_one_near_integer_iff _ _).mpr
  refine ⟨∑ j ∈ s, m j*round (v j), ?_⟩
  have he : (∑ j ∈ s, (m j : ℝ)*v j)-((∑ j ∈ s, m j*round (v j) : ℤ) : ℝ) =
      ∑ j ∈ s, (m j : ℝ)*(v j-(round (v j) : ℝ)) := by
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hh := Finset.abs_sum_le_sum_abs (fun j => (m j : ℝ)*(v j-(round (v j) : ℝ))) s
  simpa only [abs_mul, UnitAddCircle.norm_eq] using hh

end Hindman168
