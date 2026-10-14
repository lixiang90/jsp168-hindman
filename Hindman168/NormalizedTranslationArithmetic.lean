import Hindman168.SmoothRoughIntegerParts
import Hindman168.PredictionAbsorbedSmoothFactors

/-!
# Exact integer clearing of the paper's normalized translations

The rough part is not replaced by the full denominator. The signed
cofactor formula constructs an integer vector with exactly the rational
formula M Q (c_star/c_k) w_k/d. Divisibility by W is derived from the
original absorption and the proved smooth-part bound.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem absorbed_smooth_quotient (W M c S e : ℕ)
    (habs : W ^ (e + 1) * c ∣ M) (hS : S ∣ W ^ (e - 1)) :
    c * S ∣ M ∧ W ∣ M / (c * S) := by
  have hWS : W * S ∣ W ^ (e + 1) := by
    have h := mul_dvd_mul_left W hS
    rw [← pow_succ'] at h
    exact h.trans (pow_dvd_pow W (by omega : e - 1 + 1 ≤ e + 1))
  have hall : W * (c * S) ∣ M := by
    have h := (mul_dvd_mul_right hWS c).trans habs
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hd : c * S ∣ M := (dvd_mul_left (c * S) W).trans hall
  obtain ⟨t, ht⟩ := hall
  refine ⟨hd, ?_⟩
  by_cases hzero : c * S = 0
  · simp [hzero]
  · have hcS : 0 < c * S := Nat.pos_of_ne_zero hzero
    have he : M = (c * S) * (W * t) := by rw [ht]; ring
    rw [he, Nat.mul_div_cancel_left _ hcS]
    exact dvd_mul_right _ _

noncomputable def normalizedIntegerCoordinate (M c cstar w : ℕ) (D d b : ℤ) : ℤ :=
  D.sign * ((M / (c * smoothPartNat w D.natAbs) : ℕ) : ℤ) * (cstar : ℤ) * b * (D / d)

theorem normalizedIntegerCoordinate_W_divisible (W M c cstar w e : ℕ)
    (D d b : ℤ) (habs : W ^ (e + 1) * c ∣ M)
    (hS : smoothPartNat w D.natAbs ∣ W ^ (e - 1)) :
    (W : ℤ) ∣ normalizedIntegerCoordinate M c cstar w D d b := by
  have h := Int.natCast_dvd_natCast.mpr (absorbed_smooth_quotient W M c _ e habs hS).2
  unfold normalizedIntegerCoordinate
  exact (h.trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _) |>.trans
    (dvd_mul_right _ _) |>.trans (dvd_mul_right _ _)

theorem normalizedIntegerCoordinate_eq (W M c cstar w e : ℕ) (D d b : ℤ)
    (hc : 0 < c) (hD : D ≠ 0) (hd : d ≠ 0) (hdiv : d ∣ D)
    (habs : W ^ (e + 1) * c ∣ M)
    (hS : smoothPartNat w D.natAbs ∣ W ^ (e - 1)) :
    (normalizedIntegerCoordinate M c cstar w D d b : ℚ) =
      ((M * roughPartNat w D.natAbs : ℕ) : ℚ) *
        ((cstar : ℚ) / c) * ((b : ℚ) / d) := by
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hs0 : (smoothPartNat w D.natAbs : ℚ) ≠ 0 := by
    exact_mod_cast smoothPartNat_ne_zero (Int.natAbs_ne_zero.mpr hD)
  have hsign : (D.sign : ℚ) * (D : ℚ) =
      (smoothPartNat w D.natAbs : ℚ) * roughPartNat w D.natAbs := by
    have he := Int.sign_mul_self_eq_natAbs D
    rw [← smoothPartNat_mul_roughPartNat (w := w) (Int.natAbs_ne_zero.mpr hD)] at he
    exact_mod_cast he
  unfold normalizedIntegerCoordinate
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [Nat.cast_div (absorbed_smooth_quotient W M c _ e habs hS).1
    (by simpa only [Nat.cast_mul] using mul_ne_zero hc0 hs0), Int.cast_div hdiv hd0]
  simp only [Nat.cast_mul]
  calc
    _ = (M : ℚ) * cstar * b * ((D.sign : ℚ) * D) /
        ((c : ℚ) * smoothPartNat w D.natAbs * d) := by field_simp
    _ = _ := by rw [hsign]; field_simp

noncomputable def normalizedRootIntegerCoordinate (M c cstar : ℕ) (b : ℤ) : ℤ :=
  ((M / c : ℕ) : ℤ) * (cstar : ℤ) * b

theorem normalizedRootIntegerCoordinate_W_divisible (W M c cstar e : ℕ) (b : ℤ)
    (hM : 0 < M) (hc : 0 < c) (habs : W ^ (e + 1) * c ∣ M) :
    (W : ℤ) ∣ normalizedRootIntegerCoordinate M c cstar b := by
  have h := Int.natCast_dvd_natCast.mpr (absorbed_modulus_quotient_conditions W M c e hM hc habs).2.2
  exact (h.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)

theorem normalizedRootIntegerCoordinate_eq (M c cstar : ℕ) (b : ℤ)
    (hc : 0 < c) (hdiv : c ∣ M) :
    (normalizedRootIntegerCoordinate M c cstar b : ℚ) =
      (M : ℚ) * ((cstar : ℚ) / c) * b := by
  unfold normalizedRootIntegerCoordinate
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_div hdiv (by exact_mod_cast hc.ne')]
  ring

end Hindman168
