import Hindman168.PrimePoolCombine
import Hindman168.FiniteEventMixtures

/-!
# Exact harmonic-mass decomposition of actual dyadic prime pools

The unnormalized identity also holds for empty subintervals. After the
actual total harmonic mass is positive, normalization gives a probability
mixture of the original 1/p laws on all constituent dyadic intervals.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem primePoolMass_weighted_apply (A B p : ℕ) :
    primePoolHarmonicMass A B * primePoolMass A B p =
      if p ∈ primePool A B then (p : ℝ)⁻¹ else 0 := by
  rw [primePoolMass_apply, primePoolWeight]
  by_cases hp : p ∈ primePool A B
  · rw [if_pos hp, if_pos hp]
    have hH := primePoolHarmonicMass_pos ⟨p, hp⟩
    field_simp [hH.ne']
  · simp [hp]

theorem primePoolMass_weighted_split {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    primePoolHarmonicMass A C • primePoolMass A C =
      primePoolHarmonicMass A B • primePoolMass A B +
      primePoolHarmonicMass B C • primePoolMass B C := by
  ext p
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply]
  rw [primePoolMass_weighted_apply, primePoolMass_weighted_apply, primePoolMass_weighted_apply]
  by_cases hp : p ∈ primePool A C
  · obtain ⟨hAp, hpC, hprime⟩ := primePool_mem.mp hp
    by_cases hpB : p < B
    · have hleft : p ∈ primePool A B := primePool_mem.mpr ⟨hAp, hpB, hprime⟩
      have hright : p ∉ primePool B C := by
        intro h; exact hpB.not_ge (primePool_mem.mp h).1
      simp [hp, hleft, hright]
    · have hleft : p ∉ primePool A B := by
        intro h; exact hpB (primePool_mem.mp h).2.1
      have hright : p ∈ primePool B C := primePool_mem.mpr ⟨le_of_not_gt hpB, hpC, hprime⟩
      simp [hp, hleft, hright]
  · have hleft : p ∉ primePool A B := by
      intro h
      obtain ⟨hAp, hpB, hprime⟩ := primePool_mem.mp h
      exact hp (primePool_mem.mpr ⟨hAp, hpB.trans_le hBC, hprime⟩)
    have hright : p ∉ primePool B C := by
      intro h
      obtain ⟨hBp, hpC, hprime⟩ := primePool_mem.mp h
      exact hp (primePool_mem.mpr ⟨hAB.trans hBp, hpC, hprime⟩)
    simp [hp, hleft, hright]

theorem primePoolMass_weighted_dyadic_sum (a k : ℕ) :
    primePoolHarmonicMass (2 ^ a) (2 ^ (a + k)) • primePoolMass (2 ^ a) (2 ^ (a + k)) =
      ∑ e ∈ Finset.Ico a (a + k),
        primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) • primePoolMass (2 ^ e) (2 ^ (e + 1)) := by
  induction k with
  | zero => simp [primePoolHarmonicMass, primePool]
  | succ k ih =>
    have hAB : 2 ^ a ≤ 2 ^ (a + k) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hBC : 2 ^ (a + k) ≤ 2 ^ (a + k + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    rw [show a + (k + 1) = a + k + 1 by omega,
      primePoolMass_weighted_split hAB hBC, Finset.sum_Ico_succ_top (by omega), ih]

theorem primePoolHarmonicMass_dyadic_sum {a b : ℕ} (hab : a ≤ b) :
    primePoolHarmonicMass (2 ^ a) (2 ^ b) =
      ∑ e ∈ Finset.Ico a b, primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) := by
  have H : ∀ k : ℕ, primePoolHarmonicMass (2 ^ a) (2 ^ (a + k)) =
      ∑ e ∈ Finset.Ico a (a + k), primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) := by
    intro k
    induction k with
    | zero => simp [primePoolHarmonicMass, primePool]
    | succ k ih =>
      have hAB : 2 ^ a ≤ 2 ^ (a + k) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have hBC : 2 ^ (a + k) ≤ 2 ^ (a + k + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      rw [show a + (k + 1) = a + k + 1 by omega,
        primePoolHarmonicMass_split hAB hBC, Finset.sum_Ico_succ_top (by omega), ih]
  simpa only [Nat.add_sub_of_le hab] using H (b - a)

noncomputable def dyadicPoolMixWeight (a b e : ℕ) : ℝ :=
  primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) / primePoolHarmonicMass (2 ^ a) (2 ^ b)

theorem dyadicPoolMixWeight_nonneg (a b e : ℕ) : 0 ≤ dyadicPoolMixWeight a b e :=
  div_nonneg (primePoolHarmonicMass_nonneg _ _) (primePoolHarmonicMass_nonneg _ _)

theorem dyadicPoolMixWeight_total {a b : ℕ} (hab : a ≤ b)
    (hH : 0 < primePoolHarmonicMass (2 ^ a) (2 ^ b)) :
    ∑ e ∈ Finset.Ico a b, dyadicPoolMixWeight a b e = 1 := by
  simp only [dyadicPoolMixWeight]
  rw [← Finset.sum_div, ← primePoolHarmonicMass_dyadic_sum hab, div_self hH.ne']

theorem primePoolMass_dyadic_mixture {a b : ℕ} (hab : a ≤ b)
    (hH : 0 < primePoolHarmonicMass (2 ^ a) (2 ^ b)) :
    primePoolMass (2 ^ a) (2 ^ b) =
      mixture (Finset.Ico a b) (dyadicPoolMixWeight a b)
        (fun e => primePoolMass (2 ^ e) (2 ^ (e + 1))) := by
  classical
  have h := primePoolMass_weighted_dyadic_sum a (b - a)
  simp only [Nat.add_sub_of_le hab] at h
  ext p
  have hp := congrArg (fun μ : Mass ℕ => μ p) h
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply] at hp
  rw [mixture_apply]
  simp only [dyadicPoolMixWeight, div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← hp]
  field_simp [hH.ne']

end Hindman168
