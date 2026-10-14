import Hindman168.UnitTorusUniformFourierApproximation
import Mathlib.MeasureTheory.Integral.PeakFunction

/-! An actual positive normalized peak kernel under explicit product-circle Haar. -/

namespace Hindman168
open MeasureTheory
open scoped Topology

noncomputable def unitTorusPeakBase (κ : Type*) [Fintype κ] : C(UnitAddTorus κ, ℝ) :=
  ⟨fun a => (1+dist a 0)⁻¹,
    (continuous_const.add (continuous_id.dist continuous_const)).inv₀
      (fun a => ne_of_gt (by positivity : 0 < (1 : ℝ)+dist a 0))⟩

theorem unit_torus_peak_base_positive {κ : Type*} [Fintype κ] (a : UnitAddTorus κ) :
    0 < unitTorusPeakBase κ a := by
  change 0 < (1+dist a 0)⁻¹
  positivity

theorem unit_torus_peak_base_zero (κ : Type*) [Fintype κ] : unitTorusPeakBase κ 0 = 1 := by
  simp only [unitTorusPeakBase, ContinuousMap.coe_mk, dist_self, add_zero, inv_one]

theorem unit_torus_peak_base_unique_maximum {κ : Type*} [Fintype κ]
    (a : UnitAddTorus κ) (ha : a ≠ 0) : unitTorusPeakBase κ a < unitTorusPeakBase κ 0 := by
  rw [unit_torus_peak_base_zero]
  change (1+dist a 0)⁻¹ < 1
  have hd : 0 < dist a 0 := dist_pos.mpr ha
  exact (inv_lt_one₀ (by positivity : 0 < (1 : ℝ)+dist a 0)).mpr (by linarith only [hd])

noncomputable def unitTorusPeakMass (κ : Type*) [Fintype κ] (n : ℕ) : ℝ :=
  ∫ a : UnitAddTorus κ, unitTorusPeakBase κ a ^ n
    ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)

theorem unit_torus_peak_mass_positive (κ : Type*) [Fintype κ] (n : ℕ) :
    0 < unitTorusPeakMass κ n := by
  apply ((unitTorusPeakBase κ).continuous.pow n).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun a => (pow_pos (unit_torus_peak_base_positive a) n).le)
    (x := (0 : UnitAddTorus κ))
  change unitTorusPeakBase κ 0 ^ n ≠ 0
  rw [unit_torus_peak_base_zero, one_pow]
  exact one_ne_zero

noncomputable def unitTorusPeakKernel (κ : Type*) [Fintype κ] (n : ℕ) : C(UnitAddTorus κ, ℂ) :=
  ⟨fun a => ((unitTorusPeakMass κ n)⁻¹ * unitTorusPeakBase κ a ^ n : ℝ),
    Complex.continuous_ofReal.comp (continuous_const.mul ((unitTorusPeakBase κ).continuous.pow n))⟩

theorem unit_torus_peak_kernel_norm {κ : Type*} [Fintype κ] (n : ℕ) (a : UnitAddTorus κ) :
    ‖unitTorusPeakKernel κ n a‖ = (unitTorusPeakMass κ n)⁻¹ * unitTorusPeakBase κ a ^ n := by
  rw [unitTorusPeakKernel, ContinuousMap.coe_mk, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (inv_nonneg.mpr (unit_torus_peak_mass_positive κ n).le)
    (pow_nonneg (unit_torus_peak_base_positive a).le n)

theorem unit_torus_peak_kernel_norm_integral (κ : Type*) [Fintype κ] (n : ℕ) :
    (∫ a : UnitAddTorus κ, ‖unitTorusPeakKernel κ n a‖
      ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) = 1 := by
  simp_rw [unit_torus_peak_kernel_norm]
  rw [integral_const_mul]
  change (unitTorusPeakMass κ n)⁻¹ * unitTorusPeakMass κ n = 1
  exact inv_mul_cancel₀ (ne_of_gt (unit_torus_peak_mass_positive κ n))

end Hindman168
