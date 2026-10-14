import Hindman168.FiniteHaarCauchySchwarz

namespace Hindman168
variable {A : Type*} [AddCommGroup A] [Fintype A]

noncomputable def finiteHaarDifferenceDensity (r : A → ℝ) (a : A) : ℝ :=
  finiteHaarMean (fun u => r u * r (u + a))

theorem finiteHaarDifferenceDensity_nonneg (r : A → ℝ) (hr : ∀ u, 0 ≤ r u) (a : A) :
    0 ≤ finiteHaarDifferenceDensity r a :=
  finiteHaarMean_nonneg _ (fun u => mul_nonneg (hr u) (hr (u + a)))

theorem finiteHaarDifferenceDensity_total (r : A → ℝ) (hr : finiteHaarMean r = 1) :
    finiteHaarMean (finiteHaarDifferenceDensity r) = 1 := by
  unfold finiteHaarDifferenceDensity
  rw [finiteHaarMean_comm]
  simp only [finiteHaarMean_const_mul, finiteHaarMean_add_left, hr, mul_one]

theorem finiteHaarDifferenceDensity_le (r : A → ℝ) (hr : ∀ u, 0 ≤ r u)
    (ht : finiteHaarMean r = 1) (C : ℝ) (hb : ∀ u, r u ≤ C) (a : A) :
    finiteHaarDifferenceDensity r a ≤ C := by
  calc
    _ ≤ finiteHaarMean (fun u => r u * C) :=
      finiteHaarMean_mono _ _ (fun u => mul_le_mul_of_nonneg_left (hb _) (hr u))
    _ = C := by rw [finiteHaarMean_mul_const, ht, one_mul]

theorem finiteHaarDifferenceDensity_expectation (r F : A → ℝ) :
    finiteHaarMean (fun u => finiteHaarMean (fun v => r u * r v * F (v - u))) =
      finiteHaarMean (fun a => finiteHaarDifferenceDensity r a * F a) := by
  have he (u : A) : finiteHaarMean (fun v => r u * r v * F (v - u)) =
      finiteHaarMean (fun a => r u * r (u + a) * F a) := by
    simpa only [add_sub_cancel_left] using
      (finiteHaarMean_add_left (fun v => r u * r v * F (v - u)) u).symm
  simp only [he]
  rw [finiteHaarMean_comm]
  simp only [finiteHaarMean_mul_const, finiteHaarDifferenceDensity]

end Hindman168
