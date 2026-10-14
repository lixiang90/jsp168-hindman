import Hindman168.NormalizedHaarWeightError

namespace Hindman168
open scoped BigOperators

theorem harmonicCell_density_error {α : Type*} [Fintype α] [Nonempty α]
    (y : α → ℝ) (A R : ℝ) (hA : 0 < A) (hR : 0 ≤ R)
    (hy : ∀ x, A ≤ y x ∧ y x ≤ A + R) (x : α) :
    |(1 / y x) / finiteHaarMean (fun z => 1 / y z) - 1| ≤ R / A := by
  have hAR : 0 < A + R := by linarith
  have hb (z : α) : 1 / (A + R) ≤ 1 / y z ∧ 1 / y z ≤ 1 / A :=
    ⟨one_div_le_one_div_of_le (hA.trans_le (hy z).1) (hy z).2,
      one_div_le_one_div_of_le hA (hy z).1⟩
  have he : (1 / A - 1 / (A + R)) / (1 / (A + R)) = R / A := by
    field_simp
    ring
  rw [← he]
  exact normalizedHaarWeight_error (fun z => 1 / y z) _ _ (one_div_pos.mpr hAR) hb x

theorem harmonicCell_test_error {α : Type*} [Fintype α] [Nonempty α]
    (y F : α → ℝ) (A R : ℝ) (hA : 0 < A) (hR : 0 ≤ R)
    (hy : ∀ x, A ≤ y x ∧ y x ≤ A + R) (hF : ∀ x, |F x| ≤ 1) :
    |finiteHaarMean (fun x => ((1 / y x) / finiteHaarMean (fun z => 1 / y z)) * F x) -
      finiteHaarMean F| ≤ R / A :=
  finiteHaarDensity_test_error _ F _ (harmonicCell_density_error y A R hA hR hy) hF

theorem harmonicCell_conditional_expectation_error {α : Type*} [Fintype α] [Nonempty α]
    (y F : α → ℝ) (A R : ℝ) (hA : 0 < A) (hR : 0 ≤ R)
    (hy : ∀ x, A ≤ y x ∧ y x ≤ A + R) (hF : ∀ x, |F x| ≤ 1) :
    |(∑ x, (1 / y x) * F x) / (∑ x, 1 / y x) - finiteHaarMean F| ≤ R / A := by
  rw [← normalizedHaar_test_eq_ratio]
  exact harmonicCell_test_error y F A R hA hR hy hF

theorem weightedCell_test_error {ι : Type*} [Fintype ι]
    (p a b : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (ε : ℝ) (he : ∀ c, |a c - b c| ≤ ε) :
    |(∑ c, p c * a c) - ∑ c, p c * b c| ≤ ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |p c * a c - p c * b c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, p c * |a c - b c| := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hp c)]
    _ ≤ ∑ c, p c * ε := Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (he c) (hp c))
    _ = ε := by rw [← Finset.sum_mul, hs, one_mul]

theorem weightedHarmonicCell_test_error {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (y F : ι → α → ℝ) (A : ι → ℝ) (X R : ℝ) (hX : 0 < X) (hR : 0 ≤ R)
    (hA : ∀ c, X ≤ A c) (hy : ∀ c x, A c ≤ y c x ∧ y c x ≤ A c + R)
    (hF : ∀ c x, |F c x| ≤ 1) :
    |(∑ c, p c * ((∑ x, (1 / y c x) * F c x) / (∑ x, 1 / y c x))) -
      ∑ c, p c * finiteHaarMean (F c)| ≤ R / X := by
  apply weightedCell_test_error p _ _ hp hs
  intro c
  exact (harmonicCell_conditional_expectation_error (y c) (F c) (A c) R
    (hX.trans_le (hA c)) hR (hy c) (hF c)).trans
    (div_le_div_of_nonneg_left hR hX (hA c))

end Hindman168
