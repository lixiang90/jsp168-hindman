import Hindman168.PrimeAPPrefix
import Hindman168.PrimeHarmonicLower

/-!
# Actual 1/p-weighted dyadic primes are equidistributed in primitive classes

For each fixed modulus q, the normalized mass in a primitive class tends
to 1/totient(q). The mass lower bound is retained until the Abel error has
been normalized. The conclusion is uniform over any fixed finite family
of primitive residues, not a uniform PNT for growing moduli.
-/

namespace Hindman168

open Filter
open scoped Topology

theorem primeHarmonicResidue_dyadic_normalized_small {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      |primeHarmonicResidue q a (2 ^ n) (2 ^ (n + 1)) /
        primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) - 1 / q.totient| ≤ ε := by
  let δ : ℝ := ε / 32
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  filter_upwards [primeHarmonicResidue_dyadic_eventually_error hq ha haq hδ,
    primePoolHarmonicMass_dyadic_eventually_lower,
    primePoolHarmonicMass_dyadic_eventually_pos,
    dyadic_atTop.eventually (eventually_ge_atTop 2)] with n he hH hHp hn
  have hlog : 0 < Real.log (2 ^ n : ℕ) := Real.log_pos (by
    exact_mod_cast (by omega : 1 < 2 ^ n))
  have hid : primeHarmonicResidue q a (2 ^ n) (2 ^ (n + 1)) /
        primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) - 1 / q.totient =
      (primeHarmonicResidue q a (2 ^ n) (2 ^ (n + 1)) -
        primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) / q.totient) /
        primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) := by field_simp
  rw [hid, abs_div, abs_of_pos hHp]
  apply (div_le_iff₀ hHp).mpr
  calc
    _ ≤ 4 * δ / Real.log (2 ^ n : ℕ) := he
    _ = ε * (1 / (8 * Real.log (2 ^ n : ℕ))) := by dsimp [δ]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hH hε.le

theorem primeHarmonicResidue_dyadic_normalized_tendsto {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    Tendsto (fun n : ℕ => primeHarmonicResidue q a (2 ^ n) (2 ^ (n + 1)) /
      primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1))) atTop (𝓝 (1 / q.totient)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hε : 0 < (1 / (q.totient : ℝ) - b) / 2 := by linarith
    filter_upwards [primeHarmonicResidue_dyadic_normalized_small hq ha haq hε] with n hn
    have hl := (abs_le.mp hn).1
    linarith
  · intro b hb
    have hε : 0 < (b - 1 / (q.totient : ℝ)) / 2 := by linarith
    filter_upwards [primeHarmonicResidue_dyadic_normalized_small hq ha haq hε] with n hn
    have hl := (abs_le.mp hn).2
    linarith

theorem primeHarmonicResidue_dyadic_uniform_small {q : ℕ} (A : Finset ℕ)
    (hq : 1 ≤ q) (hA : ∀ a ∈ A, a.Coprime q ∧ a < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a ∈ A,
      |primeHarmonicResidue q a (2 ^ n) (2 ^ (n + 1)) /
        primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) - 1 / q.totient| ≤ ε := by
  apply (eventually_all_finset A).mpr
  intro a ha
  exact primeHarmonicResidue_dyadic_normalized_small hq (hA a ha).1 (hA a ha).2 hε

end Hindman168
