import Hindman168.PredictionQuotientLengths
import Hindman168.PrimeValuationVectors

/-!
# Actual smooth/rough parts and the good-tuple small-prime bound

The parts retain all multiplicities and split the absolute value exactly.
Excluding p^e for every prime p <= w bounds the smooth part by divisibility
into primorial(w)^(e-1); no smooth-part hypothesis is introduced.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def smoothPartNat (w n : ℕ) : ℕ :=
  if n = 0 then 0 else (n.primeFactorsList.filter (fun p => decide (p ≤ w))).prod

theorem smoothPartNat_mul_roughPartNat {w n : ℕ} (hn : n ≠ 0) :
    smoothPartNat w n * roughPartNat w n = n := by
  rw [smoothPartNat, roughPartNat, if_neg hn, if_neg hn]
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun p : ℕ => p ≤ w)
    (fun p => p) n.primeFactorsList
  simpa [not_le, Nat.prod_primeFactorsList hn] using h

theorem smoothPartNat_ne_zero {w n : ℕ} (hn : n ≠ 0) : smoothPartNat w n ≠ 0 := by
  intro hs
  have he := smoothPartNat_mul_roughPartNat (w := w) hn
  rw [hs, zero_mul] at he
  exact hn he.symm

theorem prime_dvd_smoothPartNat {w n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    p ∣ smoothPartNat w n ↔ p ≤ w ∧ p ∣ n := by
  rw [smoothPartNat, if_neg hn, prime_dvd_natListProd_iff hp]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hq' := List.mem_of_mem_filter hq
    have he : p = q := ((Nat.dvd_prime (Nat.prime_of_mem_primeFactorsList hq')).mp hpq).resolve_left hp.ne_one
    subst q
    exact ⟨by simpa only [decide_eq_true_eq] using (List.mem_filter.mp hq).2,
      Nat.dvd_of_mem_primeFactorsList hq'⟩
  · rintro ⟨hpw, hpn⟩
    exact ⟨p, List.mem_filter.mpr ⟨(Nat.mem_primeFactorsList hn).mpr ⟨hp, hpn⟩,
      by simpa using hpw⟩, dvd_refl p⟩

theorem smoothPartNat_factorization {w n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    (smoothPartNat w n).factorization p = if p ≤ w then n.factorization p else 0 := by
  by_cases hpw : p ≤ w
  · have hnot : ¬ p ∣ roughPartNat w n := by
      rw [prime_dvd_roughPartNat hn hp]
      omega
    have he := congrArg (fun v : ℕ => v.factorization p)
      (smoothPartNat_mul_roughPartNat (w := w) hn)
    rw [Nat.factorization_mul (smoothPartNat_ne_zero hn)
      (roughPartNat_pos hn).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot, add_zero] at he
    simpa only [if_pos hpw] using he
  · rw [if_neg hpw]
    apply Nat.factorization_eq_zero_of_not_dvd
    rw [prime_dvd_smoothPartNat hn hp]
    exact fun h => hpw h.1

theorem smoothPartNat_dvd_primorial_pow {w n e : ℕ} (hn : n ≠ 0)
    (havoid : ∀ p, p.Prime → p ≤ w → ¬ p ^ e ∣ n) :
    smoothPartNat w n ∣ (primorial w) ^ (e - 1) := by
  apply (Nat.factorization_le_iff_dvd (smoothPartNat_ne_zero hn)
    (pow_ne_zero _ (primorial_ne_zero w))).mp
  intro p
  by_cases hp : p.Prime
  · rw [smoothPartNat_factorization hn hp]
    by_cases hpw : p ≤ w
    · rw [if_pos hpw]
      have hlt : n.factorization p < e := by
        have hnot := havoid p hp hpw
        rw [hp.pow_dvd_iff_le_factorization hn] at hnot
        omega
      have hW : (primorial w).factorization p = 1 := by
        have h := primeValuationDivisor_factorization_apply (Nat.primesLE w) (fun _ => 1)
          (fun q hq => Nat.prime_of_mem_primesLE hq) p
        simpa only [primeValuationDivisor, pow_one, ← primorial_eq_prod_primesLE,
          if_pos (Nat.mem_primesLE.mpr ⟨hpw, hp⟩)] using h
      simpa only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hW, mul_one]
        using (show n.factorization p ≤ e - 1 by omega)
    · simp only [if_neg hpw]
      exact Nat.zero_le _
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

end Hindman168
