import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Hindman168
open scoped BigOperators

variable {ι : Type*}

noncomputable def roughHorizontalIntegerSize (S : Finset ι) (m : ι → ℤ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : ↥S => (m i : ℝ)) : EuclideanSpace ℝ ↥S)‖

theorem rough_horizontal_integer_size_nonnegative (S : Finset ι) (m : ι → ℤ) :
    0 ≤ roughHorizontalIntegerSize S m := norm_nonneg _

theorem rough_horizontal_integer_size_square (S : Finset ι) (m : ι → ℤ) :
    roughHorizontalIntegerSize S m ^ 2 = ∑ i ∈ S, (m i : ℝ)^2 := by
  classical
  unfold roughHorizontalIntegerSize
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_coe_sort S (fun i => (m i : ℝ)^2)

theorem rough_horizontal_integer_size_le_iff (S : Finset ι) (m : ι → ℤ)
    (M : ℝ) (hM : 0 ≤ M) :
    roughHorizontalIntegerSize S m ≤ M ↔ ∑ i ∈ S, (m i : ℝ)^2 ≤ M^2 := by
  rw [← rough_horizontal_integer_size_square S m]
  have hn := rough_horizontal_integer_size_nonnegative S m
  constructor <;> intro h <;> nlinarith

end Hindman168
