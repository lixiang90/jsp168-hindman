import Hindman168.SieveCutoffGrowth
import Hindman168.PrimePolynomialResidues

/-!
# A uniform small-prime residue bound proved from the interval sieve

For every sufficiently large dyadic endpoint A, all prime moduli
q <= sqrt A and all residue classes have harmonic prime probability
at most 1032/q. The numerical constant is coarse and uniform. The
proof uses the explicit cutoff and actual PNT normalization; neither
Brun--Titchmarsh nor a desired prime-count inequality is assumed.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem smallPrimeResidue_bound_of_cutoff {A q z a : ℕ} (hq : q.Prime)
    (hA : 2 ≤ A) (hz : 1 ≤ z) (hzA : z < A) (ha : a < q)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hsmall : (q : ℝ) ≤ Real.sqrt A)
    (hlogz : Real.log (A : ℝ) ≤ 32 * Real.log (z + 1 : ℕ))
    (hzpow : (z : ℝ) ^ 4 ≤ (A : ℝ) ^ (1 / 4 : ℝ))
    (hlogpow : Real.log (A : ℝ) ≤ (A : ℝ) ^ (1 / 4 : ℝ)) :
    primePoolResidueMass q A (2 * A) a ≤ 1032 / (q : ℝ) := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.mpr hAr
  have hlog : 0 ≤ Real.log (A : ℝ) :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < A))).le
  have hlogzp : 0 < Real.log (z + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < z + 1))
  have hmain : 32 * (Real.log (A : ℝ) / Real.log (z + 1 : ℕ)) / q ≤ 1024 / (q : ℝ) := by
    have hm : Real.log (A : ℝ) / Real.log (z + 1 : ℕ) ≤ 32 :=
      (div_le_iff₀ hlogzp).mpr hlogz
    have hm32 := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 32)
    have hd := div_le_div_of_nonneg_right hm32 hqr.le
    norm_num at hd
    simpa only [Nat.cast_add, Nat.cast_one] using hd
  have hquarterSquare : ((A : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hAr.le, Real.sqrt_eq_rpow]
    norm_num
  have hprod : Real.log (A : ℝ) * (z : ℝ) ^ 4 ≤ Real.sqrt A := by
    calc
      _ ≤ (A : ℝ) ^ (1 / 4 : ℝ) * (A : ℝ) ^ (1 / 4 : ℝ) :=
        mul_le_mul hlogpow hzpow (by positivity) (Real.rpow_nonneg hAr.le _)
      _ = _ := by rw [← sq, hquarterSquare]
  have hinv : Real.sqrt (A : ℝ) / A = 1 / Real.sqrt A := by
    apply (div_eq_div_iff hAr.ne' hsqrt.ne').mpr
    simpa only [one_mul, sq] using Real.sq_sqrt hAr.le
  have herr : 8 * Real.log (A : ℝ) * (z : ℝ) ^ 4 / A ≤ 8 / (q : ℝ) := by
    calc
      _ = 8 * (Real.log (A : ℝ) * (z : ℝ) ^ 4) / A := by ring
      _ ≤ 8 * Real.sqrt A / A := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by norm_num)) hAr.le
      _ = 8 / Real.sqrt A := by rw [mul_div_assoc, hinv]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hqr hsmall
  calc
    _ ≤ 8 * (Real.log (A : ℝ) / A) *
        (4 * ((A : ℝ) / q) / Real.log (z + 1 : ℕ) + (z : ℝ) ^ 4) :=
      dyadicPrime_residue_sieve_probability hq hA hz hzA ha hH
    _ = 32 * (Real.log (A : ℝ) / Real.log (z + 1 : ℕ)) / q +
        8 * Real.log (A : ℝ) * (z : ℝ) ^ 4 / A := by
      field_simp [hAr.ne']
      ring
    _ ≤ 1024 / (q : ℝ) + 8 / (q : ℝ) := add_le_add hmain herr
    _ = _ := by ring

theorem smallPrimeResidue_eventually_uniform :
    ∀ᶠ A : ℕ in atTop, ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt A →
      ∀ a < q, (1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A)) →
        primePoolResidueMass q A (2 * A) a ≤ 1032 / (q : ℝ) := by
  filter_upwards [uniformSieveCutoff_eventually] with A hA
  intro q hq hs a ha hH
  exact smallPrimeResidue_bound_of_cutoff hq hA.1 hA.2.1 hA.2.2.1 ha hH hs
    hA.2.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2

theorem dyadicSmallPrimeResidue_eventually_uniform :
    ∀ᶠ e : ℕ in atTop, ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt (2 ^ e : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ e) (2 ^ (e + 1)) a ≤ 1032 / (q : ℝ) := by
  filter_upwards [dyadic_atTop.eventually smallPrimeResidue_eventually_uniform,
    primePoolHarmonicMass_dyadic_eventually_lower] with e he hH
  intro q hq hs a ha
  simpa only [Nat.pow_succ, Nat.mul_comm] using
    he q hq hs a ha (by simpa only [Nat.pow_succ, Nat.mul_comm] using hH)

theorem exists_dyadicSmallPrimeResidue_threshold :
    ∃ e0 : ℕ, ∀ e ≥ e0, ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt (2 ^ e : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ e) (2 ^ (e + 1)) a ≤ 1032 / (q : ℝ) :=
  eventually_atTop.mp dyadicSmallPrimeResidue_eventually_uniform

theorem smallPrime_polynomial_fiber_bound {q A : ℕ} [Fact q.Prime]
    (hcap : ∀ a < q, primePoolResidueMass q A (2 * A) a ≤ 1032 / (q : ℝ))
    (f : Polynomial ℤ) (hcoeff : ¬ (q : ℤ) ∣ f.leadingCoeff) :
    event (primePoolMass A (2 * A)) (fun n => (q : ℤ) ∣ f.eval (n : ℤ)) ≤
      (f.natDegree : ℝ) * (1032 / (q : ℝ)) := by
  apply primePolynomial_divisibility_atom_bound f
    (integerPolynomial_mod_ne_zero_of_leadingCoeff f hcoeff) (by positivity)
  intro r
  rw [primePoolModMass_apply_event, ← primePoolResidueMass_eq_event]
  exact hcap r.val (ZMod.val_lt r)

end Hindman168
