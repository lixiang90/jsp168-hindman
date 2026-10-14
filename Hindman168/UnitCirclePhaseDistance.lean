import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Hindman168
open scoped Real

theorem unit_circle_phase_distance_lower (x : ℝ) :
    4*‖(x : UnitAddCircle)‖ ≤ ‖(AddCircle.toCircle (x : UnitAddCircle) : ℂ)-1‖ := by
  let u := x-(round x : ℝ)
  have hr : ((round x : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x, by simp⟩
  have hu : (u : UnitAddCircle) = (x : UnitAddCircle) := by
    rw [show u = x-(round x : ℝ) from rfl, AddCircle.coe_sub, hr, sub_zero]
  have he : (AddCircle.toCircle (x : UnitAddCircle) : ℂ) =
      Complex.exp (Complex.I*((2*Real.pi*u : ℝ) : ℂ)) := by
    rw [← hu, AddCircle.toCircle_apply_mk, Circle.coe_exp]
    simp only [div_one]
    ring_nf
  have hab : |u| ≤ (1 : ℝ)/2 := abs_sub_round x
  have hangle : |Real.pi*u| ≤ Real.pi/2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hangle
  have hcancel : (2/Real.pi)*|Real.pi*u| = 2*|u| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hcancel] at hs
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2*Real.pi*u)/2 = Real.pi*u := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_two, UnitAddCircle.norm_eq]
  change 4*|u| ≤ 2*|Real.sin (Real.pi*u)|
  linarith

theorem unit_circle_phase_natural_mul (x : ℝ) (n : ℕ) :
    (AddCircle.toCircle (((n : ℝ)*x : ℝ) : UnitAddCircle) : ℂ) =
      (AddCircle.toCircle (x : UnitAddCircle) : ℂ)^n := by
  rw [← nsmul_eq_mul, AddCircle.coe_nsmul, AddCircle.toCircle_nsmul]
  exact map_pow Circle.coeHom _ n

end Hindman168
