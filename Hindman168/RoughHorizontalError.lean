import Hindman168.RoughExactInterpolationModOne

namespace Hindman168
open scoped BigOperators

theorem rough_mod_one_integer_scale (x : ℝ) (k : ℤ) :
    ‖(((k : ℝ) * x : ℝ) : UnitAddCircle)‖ ≤ |(k : ℝ)| * ‖(x : UnitAddCircle)‖ := by
  obtain ⟨b, hb⟩ := (rough_mod_one_near_integer_iff x ‖(x : UnitAddCircle)‖).mp le_rfl
  apply (rough_mod_one_near_integer_iff _ _).mpr
  refine ⟨k * b, ?_⟩
  rw [Int.cast_mul, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

theorem rough_mod_one_remove_integer_parts {ι : Type*} (s : Finset ι)
    (x : ℝ) (c k : ι → ℤ) (u : ι → ℝ) (eps : ℝ)
    (h : ‖((x + ∑ i ∈ s, (c i : ℝ) * u i : ℝ) : UnitAddCircle)‖ ≤ eps) :
    ‖(x : UnitAddCircle)‖ ≤ eps + ∑ i ∈ s, |(c i : ℝ)| * |u i - (k i : ℝ)| := by
  obtain ⟨b, hb⟩ := (rough_mod_one_near_integer_iff _ _).mp h
  apply (rough_mod_one_near_integer_iff _ _).mpr
  refine ⟨b - ∑ i ∈ s, c i * k i, ?_⟩
  have hid : x - ((b - ∑ i ∈ s, c i * k i : ℤ) : ℝ) =
      (x + ∑ i ∈ s, (c i : ℝ) * u i - (b : ℝ)) -
        ∑ i ∈ s, (c i : ℝ) * (u i - (k i : ℝ)) := by
    simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  apply add_le_add hb
  calc
    |∑ i ∈ s, (c i : ℝ) * (u i - (k i : ℝ))| ≤
        ∑ i ∈ s, |(c i : ℝ) * (u i - (k i : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul]

theorem rough_mod_one_sample_step_transfer {t : ℕ} {p S Z theta A : ℝ}
    (ht : (t : ℝ) ≤ 2 * S) (hZ : 0 < Z) (hA : 0 ≤ A)
    (e : ℕ) (hp : p = 1 ∨ p = (t : ℝ))
    (h : ‖((p ^ e * theta : ℝ) : UnitAddCircle)‖ ≤ A * (p / Z) ^ e) :
    ‖((((t : ℝ) ^ e * theta : ℝ)) : UnitAddCircle)‖ ≤
      (2 ^ e * A) * (S / Z) ^ e := by
  have hb : ‖((((t : ℝ) ^ e * theta : ℝ)) : UnitAddCircle)‖ ≤ A * ((t : ℝ) / Z) ^ e := by
    rcases hp with rfl | rfl
    · have hs := rough_mod_one_integer_scale theta ((t : ℤ) ^ e)
      simp only [Int.cast_pow, Int.cast_natCast] at hs
      rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg t : (0 : ℝ) ≤ t) e)] at hs
      simp only [one_pow, one_mul, one_div] at h
      calc
        _ ≤ (t : ℝ) ^ e * ‖(theta : UnitAddCircle)‖ := hs
        _ ≤ (t : ℝ) ^ e * (A * Z⁻¹ ^ e) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring
    · exact h
  apply hb.trans
  calc
    A * ((t : ℝ) / Z) ^ e ≤ A * ((2 * S) / Z) ^ e := by gcongr
    _ = (2 ^ e * A) * (S / Z) ^ e := by rw [mul_div_assoc, mul_pow]; ring

theorem rough_horizontal_tail_error {p Z B A c err : ℝ}
    (hp : 0 ≤ p) (hZ : 0 < Z) (hpZ : p ≤ Z) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (e n : ℕ) (hc : |c| ≤ B * p ^ n) (herr : |err| ≤ A * Z⁻¹ ^ (e + n)) :
    |p ^ e * c| * |err| ≤ (B * A) * (p / Z) ^ e := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hp e)]
  have hr : (p / Z) ^ n ≤ 1 := pow_le_one₀ (div_nonneg hp hZ.le) ((div_le_one hZ).mpr hpZ)
  calc
    (p ^ e * |c|) * |err| ≤ (p ^ e * (B * p ^ n)) * (A * Z⁻¹ ^ (e + n)) := by gcongr
    _ = ((B * A) * (p / Z) ^ e) * (p / Z) ^ n := by
      rw [pow_add, div_eq_mul_inv, mul_pow, mul_pow]
      ring
    _ ≤ ((B * A) * (p / Z) ^ e) * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := mul_one _

theorem rough_mod_one_descending_coefficient {ι : Type*} (s : Finset ι)
    (p e : ℕ) (theta Z A0 : ℝ) (c k : ι → ℤ) (u A B : ι → ℝ) (n : ι → ℕ)
    (hZ : 0 < Z) (hpZ : (p : ℝ) ≤ Z)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hc : ∀ i ∈ s, |(c i : ℝ)| ≤ B i * (p : ℝ) ^ n i)
    (hu : ∀ i ∈ s, |u i - (k i : ℝ)| ≤ A i * Z⁻¹ ^ (e + n i))
    (hobs : ‖(((p : ℝ) ^ e * (theta + ∑ i ∈ s, (c i : ℝ) * u i) : ℝ) : UnitAddCircle)‖ ≤
      A0 * ((p : ℝ) / Z) ^ e) :
    ‖(((p : ℝ) ^ e * theta : ℝ) : UnitAddCircle)‖ ≤
      (A0 + ∑ i ∈ s, B i * A i) * ((p : ℝ) / Z) ^ e := by
  have ho : ‖(((p : ℝ) ^ e * theta +
      ∑ i ∈ s, (((p : ℤ) ^ e * c i : ℤ) : ℝ) * u i : ℝ) : UnitAddCircle)‖ ≤
      A0 * ((p : ℝ) / Z) ^ e := by
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_add, Finset.mul_sum, mul_assoc] using hobs
  have hb := rough_mod_one_remove_integer_parts s ((p : ℝ) ^ e * theta)
    (fun i => (p : ℤ) ^ e * c i) k u (A0 * ((p : ℝ) / Z) ^ e) ho
  apply hb.trans
  calc
    _ ≤ A0 * ((p : ℝ) / Z) ^ e +
        ∑ i ∈ s, (B i * A i) * ((p : ℝ) / Z) ^ e := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i hi
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
        rough_horizontal_tail_error (Nat.cast_nonneg p) hZ hpZ (hB i hi) (hA i hi)
          e (n i) (hc i hi) (hu i hi)
    _ = _ := by rw [add_mul, Finset.sum_mul]

end Hindman168
