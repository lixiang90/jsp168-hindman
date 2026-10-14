import Hindman168.ActualDivisorRowCRT
import Hindman168.FiniteWeightedErrors

/-!
# Base-residue transfer for the original integer masks

The modulus is exactly the original divisor product. Its normalized
event error is at most V^q times the original base-residue L1 error.
Averaging the independent divisor-mask expansion gives the same bound
for the complete weighted mask test, without a supplied mask identity.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem base_normalized_divisor_count_error {q d : ℕ} (k : Fin q → ℕ)
    (hk : ∀ u, k u ≠ 0) (c : Fin q → Fin d → ℤ) (μ : Mass (Fin d → ℤ))
    (V : ℕ) (hV : ∀ u, k u ≤ V) (ε : ℝ) (hε : 0 ≤ ε)
    (hresidue :
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr (fun u _ => hk u)⟩
      distance (μ.mapDomain (fun x j => (x j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ ε) :
    |((∏ u, k u : ℕ) : ℝ) * event μ (fun x => ∀ u, (k u : ℤ) ∣ ∑ j, c u j * x j) -
      normalizedDivisorRowCount k c| ≤ ((V ^ q : ℕ) : ℝ) * ε := by
  classical
  letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr (fun u _ => hk u)⟩
  let stat := fun x : Fin d → ℤ => fun j => (x j : ZMod (∏ u, k u))
  let E := fun x => residueRowSystem (∏ u, k u) q d k
    (fun u => Finset.dvd_prod_of_mem k (Finset.mem_univ u)) c x = 0
  have he : event (μ.mapDomain stat) E =
      event μ (fun x => ∀ u, (k u : ℤ) ∣ ∑ j, c u j * x j) := by
    rw [event_map]
    congr 1
    funext x
    exact propext (residueRowSystem_int_zero_iff _ q d k _ c x)
  have h := (event_difference_le_distance (μ.mapDomain stat)
    (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) E).trans hresidue
  rw [he] at h
  rw [normalizedDivisorRowCount_of_ne_zero k (NeZero.ne _) c, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hprod : ((∏ u, k u : ℕ) : ℝ) ≤ ((V ^ q : ℕ) : ℝ) := by
    exact_mod_cast (show (∏ u, k u) ≤ V ^ q from by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_le_prod' (s := Finset.univ) (f := k) (g := fun _ => V) (fun u _ => hV u))
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hprod hε)

theorem weighted_integer_masks_base_error {q d : ℕ} (ρ : Fin q → Mass ℕ)
    (hρ : ∀ u k, 0 ≤ ρ u k) (htρ : ∀ u, total (ρ u) = 1)
    (μ : Mass (Fin d → ℤ)) (c : Fin q → Fin d → ℤ) (V : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : ∀ k ∈ (piMass ρ).support, ∀ u, k u ≠ 0 ∧ k u ≤ V)
    (hresidue : ∀ k, (hk : k ∈ (piMass ρ).support) →
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr (fun u _ => (hs k hk u).1)⟩
      distance (μ.mapDomain (fun x j => (x j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ ε) :
    |expectation μ (fun x => ∏ u, integerDivisorMask (ρ u) (∑ j, c u j * x j)) -
      expectation (piMass ρ) (fun k => normalizedDivisorRowCount k c)| ≤ ((V ^ q : ℕ) : ℝ) * ε := by
  rw [integerDivisorMask_product_expectation]
  have h := expectation_difference_support_bound (piMass ρ) (piMass_nonneg ρ hρ)
    (fun k => ((∏ u, k u : ℕ) : ℝ) * event μ (fun x => ∀ u, (k u : ℤ) ∣ ∑ j, c u j * x j))
    (fun k => normalizedDivisorRowCount k c) (((V ^ q : ℕ) : ℝ) * ε)
    (fun k hk => base_normalized_divisor_count_error k (fun u => (hs k hk u).1)
      c μ V (fun u => (hs k hk u).2) ε hε (hresidue k hk))
  simpa only [piMass_total_one ρ htρ, one_mul] using h

end Hindman168
