import Hindman168.PowerUnitValuations
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform geometric bounds for actual prime valuation masses

The ratio p^(-s) is bounded by 1/p for s>1. Its normalized geometric
law is an actual countable PMF, and every valuation atom is at most p^(-a).
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def primeValuationMass (s : ℝ) (p a : ℕ) : ℝ :=
  (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ a

theorem primeInversePower_pos_le {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : 2 ≤ p) :
    0 < (p : ℝ) ^ (-s) ∧ (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  simpa only [Real.rpow_neg_one] using
    Real.rpow_le_rpow_of_exponent_le hpR.le (by linarith : -s ≤ -1)

theorem primeInversePower_lt_one {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) ^ (-s) < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact (primeInversePower_pos_le hs hp).2.trans_lt (inv_lt_one_of_one_lt₀ hpR)

theorem primeValuationMass_nonneg {s : ℝ} (hs : 1 < s) {p : ℕ}
    (hp : 2 ≤ p) (a : ℕ) : 0 ≤ primeValuationMass s p a := by
  exact mul_nonneg (sub_nonneg.mpr (primeInversePower_lt_one hs hp).le)
    (pow_nonneg (primeInversePower_pos_le hs hp).1.le _)

theorem primeValuationMass_hasSum {s : ℝ} (hs : 1 < s) {p : ℕ}
    (hp : 2 ≤ p) : HasSum (primeValuationMass s p) 1 := by
  have hr0 := (primeInversePower_pos_le hs hp).1.le
  have hr1 := primeInversePower_lt_one hs hp
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (1 - (p : ℝ) ^ (-s))
  change HasSum (fun a : ℕ => (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ a) 1
  simpa only [mul_inv_cancel₀ (sub_pos.mpr hr1).ne'] using h

noncomputable def primeValuationPMF (s : ℝ) (hs : 1 < s)
    (p : ℕ) (hp : 2 ≤ p) : PMF ℕ :=
  ⟨fun a => ENNReal.ofReal (primeValuationMass s p a), by
    apply ENNReal.hasSum_coe.mpr
    simpa using (primeValuationMass_hasSum hs hp).toNNReal
      (fun a => primeValuationMass_nonneg hs hp a)⟩

theorem primeValuationPMF_apply (s : ℝ) (hs : 1 < s) (p : ℕ) (hp : 2 ≤ p) (a : ℕ) :
    primeValuationPMF s hs p hp a = ENNReal.ofReal (primeValuationMass s p a) := rfl

theorem primeValuationMass_le_inverse_pow {s : ℝ} (hs : 1 < s) {p : ℕ}
    (hp : 2 ≤ p) (a : ℕ) : primeValuationMass s p a ≤ ((p : ℝ) ^ a)⁻¹ := by
  have hr := primeInversePower_pos_le hs hp
  calc
    primeValuationMass s p a ≤ ((p : ℝ) ^ (-s)) ^ a :=
      mul_le_of_le_one_left (pow_nonneg hr.1.le _) (by linarith [hr.1])
    _ ≤ ((p : ℝ)⁻¹) ^ a := by gcongr; exact hr.2
    _ = ((p : ℝ) ^ a)⁻¹ := inv_pow _ _

theorem powerUnitPMF_prime_valuation {s : ℝ} (hs : 1 < s)
    (W p : ℕ) (hp : p.Prime) (hW : p.Coprime W) :
    (powerUnitPMF s hs W).map (fun n => n.factorization p) =
      primeValuationPMF s hs p hp.two_le := by
  ext a
  rw [powerUnitPMF_map_apply, primeValuationPMF_apply]
  congr 1
  unfold primeValuationMass
  refine (tsum_congr (fun n => ?_)).trans
    (powerUnitProbability_valuation_tsum hs W p a hp hW)
  by_cases h : n.factorization p = a
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

end Hindman168
