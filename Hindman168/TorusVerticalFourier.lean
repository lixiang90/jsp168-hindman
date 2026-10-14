import Hindman168.UnitTorusUniformFourierApproximation
import Mathlib.MeasureTheory.Group.Integral

/-! Explicit central Fourier integration under normalized product circle Haar.
The action laws below are equations, not an assumed inverse theorem. -/

namespace Hindman168
open MeasureTheory

theorem unit_torus_fourier_argument_add {κ : Type*} [Fintype κ]
    (k : κ → ℤ) (a b : UnitAddTorus κ) :
    UnitAddTorus.mFourier k (a+b) = UnitAddTorus.mFourier k a * UnitAddTorus.mFourier k b := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem unit_torus_fourier_neg_argument {κ : Type*} [Fintype κ]
    (k : κ → ℤ) (a : UnitAddTorus κ) :
    UnitAddTorus.mFourier (-k) (-a) = UnitAddTorus.mFourier k a := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    neg_zsmul, smul_neg, neg_neg]

theorem unit_torus_fourier_point_norm {κ : Type*} [Fintype κ]
    (k : κ → ℤ) (a : UnitAddTorus κ) : ‖UnitAddTorus.mFourier k a‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

theorem unit_torus_nonzero_fourier_exists {κ : Type*} [Fintype κ]
    (k : κ → ℤ) (hk : k ≠ 0) : ∃ a : UnitAddTorus κ, UnitAddTorus.mFourier k a ≠ 1 := by
  by_contra h
  push Not at h
  have hi := unit_torus_fourier_haar_integral k
  rw [if_neg hk] at hi
  have he : (fun a : UnitAddTorus κ => UnitAddTorus.mFourier k a) = fun _ => (1 : ℂ) :=
    funext h
  rw [he] at hi
  have h1 : (∫ _ : UnitAddTorus κ, (1 : ℂ)
      ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) = 1 := by simp
  rw [h1] at hi
  exact one_ne_zero hi

noncomputable def torusVerticalFourierCoefficient {κ X : Type*} [Fintype κ]
    (action : UnitAddTorus κ → X → X) (k : κ → ℤ) (F : X → ℂ) (q : X) : ℂ :=
  ∫ a : UnitAddTorus κ, UnitAddTorus.mFourier (-k) a * F (action a q)
    ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)

theorem torus_vertical_fourier_coefficient_bound {κ X : Type*} [Fintype κ]
    (action : UnitAddTorus κ → X → X) (k : κ → ℤ) (F : X → ℂ) (q : X)
    (B : ℝ) (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖torusVerticalFourierCoefficient action k F q‖ ≤ B := by
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : κ => AddCircle.haarAddCircle))
    (Filter.Eventually.of_forall (fun a => show
      ‖UnitAddTorus.mFourier (-k) a * F (action a q)‖ ≤ B by
        rw [norm_mul, unit_torus_fourier_point_norm, one_mul]
        exact hB _))
  simpa only [torusVerticalFourierCoefficient, Measure.real, measure_univ,
    ENNReal.toReal_one, mul_one] using h

theorem torus_vertical_fourier_coefficient_equivariant {κ X : Type*} [Fintype κ]
    (action : UnitAddTorus κ → X → X)
    (hadd : ∀ a b q, action (a+b) q = action a (action b q))
    (k : κ → ℤ) (F : X → ℂ) (q : X) (b : UnitAddTorus κ) :
    torusVerticalFourierCoefficient action k F (action b q) =
      UnitAddTorus.mFourier k b * torusVerticalFourierCoefficient action k F q := by
  let μ : Measure (UnitAddTorus κ) := Measure.pi (fun _ : κ => AddCircle.haarAddCircle)
  let f := fun a : UnitAddTorus κ => UnitAddTorus.mFourier (-k) (a-b) * F (action a q)
  calc
    _ = ∫ a, f (a+b) ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      simp only [f, add_sub_cancel_right, hadd]
    _ = ∫ a, f a ∂μ := integral_add_right_eq_self f b
    _ = ∫ a, UnitAddTorus.mFourier k b *
        (UnitAddTorus.mFourier (-k) a * F (action a q)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      dsimp only [f]
      rw [sub_eq_add_neg, unit_torus_fourier_argument_add, unit_torus_fourier_neg_argument]
      ring
    _ = _ := integral_const_mul _ _

theorem torus_vertical_fourier_coefficient_of_eigen {κ X : Type*} [Fintype κ]
    (action : UnitAddTorus κ → X → X) (j k : κ → ℤ) (F : X → ℂ)
    (heigen : ∀ a q, F (action a q) = UnitAddTorus.mFourier k a * F q) (q : X) :
    torusVerticalFourierCoefficient action j F q = if k=j then F q else 0 := by
  unfold torusVerticalFourierCoefficient
  have he : (fun a : UnitAddTorus κ => UnitAddTorus.mFourier (-j) a * F (action a q)) =
      fun a => UnitAddTorus.mFourier (k-j) a * F q := by
    funext a
    rw [heigen, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  rw [he, integral_mul_const, unit_torus_fourier_haar_integral]
  simp only [sub_eq_zero]
  split_ifs <;> simp only [one_mul, zero_mul]

end Hindman168
