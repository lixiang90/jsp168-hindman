import Hindman168.RoughRationalExactness

namespace Hindman168

noncomputable def roughDenominatorSubring (W : ℕ) : Subring ℚ where
  carrier := {x | ∃ k : ℕ, ∃ a : ℤ, (W : ℚ) ^ k * x = a}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro x y ⟨k, a, ha⟩ ⟨l, b, hb⟩
    refine ⟨k + l, (W : ℤ) ^ l * a + (W : ℤ) ^ k * b, ?_⟩
    push_cast
    rw [pow_add]
    linear_combination (W : ℚ) ^ l * ha + (W : ℚ) ^ k * hb
  mul_mem' := by
    rintro x y ⟨k, a, ha⟩ ⟨l, b, hb⟩
    refine ⟨k + l, a * b, ?_⟩
    push_cast
    rw [pow_add]
    calc
      (W : ℚ) ^ k * W ^ l * (x * y) = (W ^ k * x) * (W ^ l * y) := by ring
      _ = _ := by rw [ha, hb]
  neg_mem' := by
    rintro x ⟨k, a, ha⟩
    exact ⟨k, -a, by simpa only [mul_neg, Int.cast_neg] using congrArg Neg.neg ha⟩

theorem roughDenominatorSubring_mem_of_dvd (W D k : ℕ) (hD : D ∣ W ^ k)
    (x : ℚ) (hx : ∃ a : ℤ, (D : ℚ) * x = a) : x ∈ roughDenominatorSubring W := by
  obtain ⟨c, hc⟩ := hD
  obtain ⟨a, ha⟩ := hx
  refine ⟨k, (c : ℤ) * a, ?_⟩
  have hcr : (W : ℚ) ^ k = D * c := by exact_mod_cast hc
  push_cast
  rw [hcr]
  linear_combination (c : ℚ) * ha

theorem roughDenominatorSubring_inverse (W m k : ℕ) (hm : m ≠ 0) (hdiv : m ∣ W ^ k) :
    (m : ℚ)⁻¹ ∈ roughDenominatorSubring W := by
  apply roughDenominatorSubring_mem_of_dvd W m k hdiv
  exact ⟨1, by simp only [mul_inv_cancel₀ (by exact_mod_cast hm : (m : ℚ) ≠ 0), Int.cast_one]⟩

theorem roughDenominatorSubring_integer_of_rough_power {w t : ℕ}
    (ht : (primorial w).Coprime t) (e : ℕ) {x : ℚ}
    (hx : x ∈ roughDenominatorSubring (primorial w))
    (he : ∃ b : ℤ, (t : ℚ) ^ e * x = b) : ∃ a : ℤ, x = a := by
  obtain ⟨k, a, ha⟩ := hx
  exact rough_smooth_denominator_integer_cancel k e (dvd_refl _) ht
    ⟨a, by simpa only [Nat.cast_pow] using ha⟩ he

end Hindman168
