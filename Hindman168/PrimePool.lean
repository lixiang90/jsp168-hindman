import Hindman168.FiniteProbability
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Actual harmonic prime pools and arbitrarily large dyadic pool mass

The finite pool contains all primes in [A,B). The law is proportional to
1/p, with its genuine PMF and maximum atom verified. Divergence of the
prime reciprocal series proves existence of arbitrarily large harmonic
mass with any dyadic lower endpoint. Residue equidistribution is not
claimed from divergence or Dirichlet's theorem.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

def primePool (A B : ℕ) : Finset ℕ := (Finset.Ico A B).filter Nat.Prime

noncomputable def primePoolHarmonicMass (A B : ℕ) : ℝ :=
  ∑ p ∈ primePool A B, (p : ℝ)⁻¹

theorem primePool_mem {A B p : ℕ} : p ∈ primePool A B ↔ A ≤ p ∧ p < B ∧ p.Prime := by
  simp only [primePool, Finset.mem_filter, Finset.mem_Ico, and_assoc]

theorem primePoolHarmonicMass_nonneg (A B : ℕ) : 0 ≤ primePoolHarmonicMass A B :=
  Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem primePoolHarmonicMass_pos {A B : ℕ} (hP : (primePool A B).Nonempty) :
    0 < primePoolHarmonicMass A B := by
  apply Finset.sum_pos
  · intro p hp
    exact inv_pos.mpr (by exact_mod_cast (primePool_mem.mp hp).2.2.pos)
  · exact hP

noncomputable def primePoolWeight (A B p : ℕ) : ℝ :=
  if p ∈ primePool A B then (p : ℝ)⁻¹ / primePoolHarmonicMass A B else 0

noncomputable def primePoolMass (A B : ℕ) : FiniteMass.Mass ℕ :=
  Finsupp.onFinset (primePool A B) (primePoolWeight A B) (by
    intro p hp
    by_contra hn
    exact hp (if_neg hn))

theorem primePoolMass_apply (A B p : ℕ) : primePoolMass A B p = primePoolWeight A B p := rfl

theorem primePoolMass_support (A B : ℕ) : (primePoolMass A B).support ⊆ primePool A B :=
  Finsupp.support_onFinset_subset

theorem primePoolMass_nonneg (A B p : ℕ) : 0 ≤ primePoolMass A B p := by
  rw [primePoolMass_apply, primePoolWeight]
  split_ifs
  · exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (primePoolHarmonicMass_nonneg A B)
  · exact le_rfl

theorem primePoolMass_total {A B : ℕ} (hH : 0 < primePoolHarmonicMass A B) :
    FiniteMass.total (primePoolMass A B) = 1 := by
  rw [FiniteMass.total_eq_sum _ (primePoolMass_support A B)]
  simp only [primePoolMass_apply, primePoolWeight,
    Finset.sum_congr rfl (fun p hp => if_pos hp), ← Finset.sum_div]
  exact div_self hH.ne'

noncomputable def primePoolPMF (A B : ℕ) (hH : 0 < primePoolHarmonicMass A B) : PMF ℕ :=
  FiniteMass.toPMF (primePoolMass A B) (primePoolMass_nonneg A B) (primePoolMass_total hH)

theorem primePoolPMF_apply (A B : ℕ) (hH : 0 < primePoolHarmonicMass A B) (p : ℕ) :
    primePoolPMF A B hH p = ENNReal.ofReal (primePoolWeight A B p) := rfl

theorem primePool_max_atom {A B : ℕ} (hA : 0 < A) (hH : 0 < primePoolHarmonicMass A B) (p : ℕ) :
    primePoolMass A B p ≤ 1 / ((A : ℝ) * primePoolHarmonicMass A B) := by
  rw [primePoolMass_apply, primePoolWeight]
  by_cases hp : p ∈ primePool A B
  · rw [if_pos hp]
    have hAr : (0 : ℝ) < A := by exact_mod_cast hA
    have hpA : (A : ℝ) ≤ p := by exact_mod_cast (primePool_mem.mp hp).1
    have h := div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le hAr hpA) hH.le
    simpa only [one_div, div_eq_mul_inv, mul_inv_rev, one_mul, mul_one, mul_comm, mul_assoc] using h
  · rw [if_neg hp]
    positivity

noncomputable def primeReciprocal (n : ℕ) : ℝ := if n.Prime then (n : ℝ)⁻¹ else 0

theorem primeReciprocal_nonneg (n : ℕ) : 0 ≤ primeReciprocal n := by
  unfold primeReciprocal
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · exact le_rfl

theorem primeReciprocal_not_summable : ¬ Summable primeReciprocal := by
  have he : primeReciprocal = Set.indicator {p : ℕ | p.Prime} (fun n => (1 : ℝ) / n) := by
    funext n
    by_cases hn : n.Prime
    · simp [primeReciprocal, hn]
    · simp [primeReciprocal, hn]
  rw [he]
  exact not_summable_one_div_on_primes

theorem primeReciprocal_partial_sums_atTop :
    Tendsto (fun B : ℕ => ∑ n ∈ Finset.range B, primeReciprocal n) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg primeReciprocal_nonneg).mp
    primeReciprocal_not_summable

theorem primePoolHarmonicMass_eq_tail {A B : ℕ} (hAB : A ≤ B) :
    primePoolHarmonicMass A B =
      (∑ n ∈ Finset.range B, primeReciprocal n) - ∑ n ∈ Finset.range A, primeReciprocal n := by
  unfold primePoolHarmonicMass primePool
  rw [Finset.sum_filter]
  exact Finset.sum_Ico_eq_sub _ hAB

theorem dyadic_atTop : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2)

theorem exists_large_dyadic_prime_mass (a : ℕ) (H : ℝ) :
    ∃ b : ℕ, a < b ∧ H ≤ primePoolHarmonicMass (2 ^ a) (2 ^ b) := by
  have ht := primeReciprocal_partial_sums_atTop.comp dyadic_atTop
  obtain ⟨b, hb, hh⟩ := ((eventually_ge_atTop (a + 1)).and
    (ht.eventually (eventually_ge_atTop
      (H + ∑ n ∈ Finset.range (2 ^ a), primeReciprocal n)))).exists
  have hab : a < b := by omega
  refine ⟨b, hab, ?_⟩
  rw [primePoolHarmonicMass_eq_tail (Nat.pow_le_pow_right (by decide : 0 < 2) hab.le)]
  simp only [Function.comp_apply] at hh
  linarith

theorem exists_dyadic_prime_pool (L : ℕ) (H : ℝ) :
    ∃ a b : ℕ, a < b ∧ L ≤ 2 ^ a ∧ H ≤ primePoolHarmonicMass (2 ^ a) (2 ^ b) := by
  obtain ⟨a, ha⟩ := (dyadic_atTop.eventually (eventually_ge_atTop L)).exists
  obtain ⟨b, hb, hh⟩ := exists_large_dyadic_prime_mass a H
  exact ⟨a, b, hb, ha, hh⟩

end Hindman168
