import Hindman168.RoughSmoothQuotient

namespace Hindman168

theorem rough_smooth_integer_dvd_primorial_power {w m : ℕ} (hm : m ≠ 0)
    (hsmooth : ∀ p, p.Prime → p ∣ m → p ≤ w) : m ∣ (primorial w) ^ m := by
  apply (Nat.dvd_pow_self_iff hm (primorial_ne_zero w)).mpr
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact hpp.mem_primeFactors
    (hpp.dvd_primorial_iff.mpr (hsmooth p hpp (Nat.dvd_of_mem_primeFactors hp)))
    (primorial_ne_zero w)

theorem roughDenominatorSubring_den_dvd {W : ℕ} (hW : W ≠ 0) {x : ℚ}
    (hx : x ∈ roughDenominatorSubring W) : ∃ k : ℕ, x.den ∣ W ^ k := by
  obtain ⟨k, a, ha⟩ := hx
  have hq : ((W ^ k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero k hW
  have he : x = Rat.divInt a ((W ^ k : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    apply (eq_div_iff hq).mpr
    simpa only [Nat.cast_pow, mul_comm] using ha
  refine ⟨k, ?_⟩
  have hd := Rat.den_dvd a ((W ^ k : ℕ) : ℤ)
  rw [← he] at hd
  exact_mod_cast hd

theorem roughDenominatorSubring_prime_support {w : ℕ} {x : ℚ}
    (hx : x ∈ roughDenominatorSubring (primorial w)) :
    ∀ p, p.Prime → p ∣ x.den → p ≤ w := by
  obtain ⟨k, hk⟩ := roughDenominatorSubring_den_dvd (primorial_ne_zero w) hx
  intro p hp hpx
  exact hp.dvd_primorial_iff.mp (hp.dvd_of_dvd_pow (hpx.trans hk))

theorem rough_smooth_quotient_prime_support {w D m : ℕ}
    (hD : D ≠ 0) (hDw : D ≤ w) (hm : m ≠ 0)
    (hmW : ∀ p, p.Prime → p ∣ m → p ≤ w) (e : ℕ)
    (t : ℤ) (R M : Polynomial ℚ) (P : Polynomial ℤ)
    (hclear : Polynomial.C (D : ℚ) * R = P.map (Int.castRingHom ℚ))
    (hfactor : R = (Polynomial.C (t : ℚ) + Polynomial.C (m : ℚ) * Polynomial.X) ^ e * M) :
    ∀ j p, p.Prime → p ∣ (M.coeff j).den → p ≤ w := by
  intro j
  exact roughDenominatorSubring_prime_support
    (rough_smooth_quotient_coeff_mem (primorial w) D w m m e
      (fixed_integer_dvd_primorial_power hD hDw) hm
      (rough_smooth_integer_dvd_primorial_power hm hmW) t R M P hclear hfactor j)

end Hindman168
