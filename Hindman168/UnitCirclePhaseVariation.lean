import Hindman168.UnitCirclePhaseDistance
import Hindman168.UnitCircleProgressionHitCount

namespace Hindman168

theorem unit_circle_phase_distance_upper (x : ℝ) :
    ‖(AddCircle.toCircle (x : UnitAddCircle) : ℂ)-1‖ ≤ 2*Real.pi*|x| := by
  have he : (AddCircle.toCircle (x : UnitAddCircle) : ℂ) =
      Complex.exp (Complex.I*((2*Real.pi*x : ℝ) : ℂ)) := by
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    simp only [div_one]
    ring_nf
  rw [he]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*x)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)] using hh

theorem unit_circle_phase_difference_distance (x y : ℝ) :
    ‖(AddCircle.toCircle (x : UnitAddCircle) : ℂ)-(AddCircle.toCircle (y : UnitAddCircle) : ℂ)‖ =
      ‖(AddCircle.toCircle ((x-y : ℝ) : UnitAddCircle) : ℂ)-1‖ := by
  have he : (AddCircle.toCircle (x : UnitAddCircle) : ℂ)-(AddCircle.toCircle (y : UnitAddCircle) : ℂ) =
      (AddCircle.toCircle (y : UnitAddCircle) : ℂ)*
        ((AddCircle.toCircle ((x-y : ℝ) : UnitAddCircle) : ℂ)-1) := by
    rw [mul_sub, mul_one, ← Circle.coe_mul, ← AddCircle.toCircle_add, ← AddCircle.coe_add]
    simp only [add_sub_cancel]
  rw [he, norm_mul, Circle.norm_coe, one_mul]

theorem unit_circle_phase_integer_translate (x : ℝ) (m : ℤ) :
    AddCircle.toCircle ((x-(m : ℝ) : ℝ) : UnitAddCircle) = AddCircle.toCircle (x : UnitAddCircle) := by
  rw [unit_circle_integer_translate]

end Hindman168
