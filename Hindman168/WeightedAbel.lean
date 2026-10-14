import Hindman168.PrimePool
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient

/-!
# Finite Abel error bound and the log-to-harmonic weight conversion

The bound uses actual signed prefix sums, including both endpoint terms.
No differentiability or infinite-sum interchange is needed.
-/

namespace Hindman168

open scoped BigOperators

theorem weighted_sum_abs_le_prefix_bound {A B : ℕ} (f g : ℕ → ℝ) {T : ℝ}
    (hAB : A < B) (hg : ∀ i ∈ Finset.Icc A (B - 1), 0 ≤ g i)
    (hm : ∀ i ∈ Finset.Ico A (B - 1), g (i + 1) ≤ g i)
    (hf : ∀ n ∈ Finset.Icc A B, |∑ i ∈ Finset.range n, f i| ≤ T) :
    |∑ i ∈ Finset.Ico A B, g i * f i| ≤ 2 * T * g A := by
  have hle : A ≤ B - 1 := by omega
  have hgA := hg A (Finset.mem_Icc.mpr ⟨le_rfl, hle⟩)
  have hgB := hg (B - 1) (Finset.mem_Icc.mpr ⟨hle, le_rfl⟩)
  have hfA := hf A (Finset.mem_Icc.mpr ⟨le_rfl, hAB.le⟩)
  have hfB := hf B (Finset.mem_Icc.mpr ⟨hAB.le, le_rfl⟩)
  have htel : (∑ i ∈ Finset.Ico A (B - 1), (g i - g (i + 1))) = g A - g (B - 1) := by
    have ht := Finset.sum_Ico_sub g hle
    rw [Finset.sum_sub_distrib] at ht ⊢
    linarith
  have hparts := Finset.sum_Ico_by_parts g f hAB
  simp only [smul_eq_mul] at hparts
  have hsub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  rw [hparts]
  calc
    _ ≤ |g (B - 1) * (∑ i ∈ Finset.range B, f i) -
          g A * (∑ i ∈ Finset.range A, f i)| +
        |∑ i ∈ Finset.Ico A (B - 1), (g (i + 1) - g i) * (∑ j ∈ Finset.range (i + 1), f j)| :=
      hsub _ _
    _ ≤ |g (B - 1) * (∑ i ∈ Finset.range B, f i)| +
        |g A * (∑ i ∈ Finset.range A, f i)| +
        ∑ i ∈ Finset.Ico A (B - 1), |(g (i + 1) - g i) * (∑ j ∈ Finset.range (i + 1), f j)| :=
      add_le_add (hsub _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ g (B - 1) * T + g A * T +
        ∑ i ∈ Finset.Ico A (B - 1), (g i - g (i + 1)) * T := by
      apply add_le_add
      · simp only [abs_mul, abs_of_nonneg hgA, abs_of_nonneg hgB]
        exact add_le_add (mul_le_mul_of_nonneg_left hfB hgB) (mul_le_mul_of_nonneg_left hfA hgA)
      · apply Finset.sum_le_sum
        intro i hi
        have him := Finset.mem_Ico.mp hi
        rw [abs_mul, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm i hi))]
        exact mul_le_mul_of_nonneg_left
          (hf (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (sub_nonneg.mpr (hm i hi))
    _ = 2 * T * g A := by rw [← Finset.sum_mul, htel]; ring

noncomputable def inversePrimeLogWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.log n)

theorem inversePrimeLogWeight_pos {n : ℕ} (hn : 2 ≤ n) : 0 < inversePrimeLogWeight n := by
  apply one_div_pos.mpr
  have hnr : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  exact mul_pos (by exact_mod_cast (by omega : 0 < n)) (Real.log_pos hnr)

theorem inversePrimeLogWeight_antitone {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    inversePrimeLogWeight m ≤ inversePrimeLogWeight n := by
  have hnr : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (Real.log_pos hnr))
  exact mul_le_mul hnmR (Real.log_le_log (by linarith) hnmR)
    (Real.log_pos hnr).le (Nat.cast_nonneg m)

noncomputable def primeHarmonicResidue (q a A B : ℕ) : ℝ :=
  ∑ p ∈ primePool A B, if p % q = a then (p : ℝ)⁻¹ else 0

noncomputable def primeResidueLogCoefficient (q a p : ℕ) : ℝ :=
  if p.Prime then (if p % q = a then Real.log p else 0) - Real.log p / q.totient else 0

theorem primeHarmonicResidue_defect_weighted (q a A B : ℕ) (hq : 1 ≤ q) :
    primeHarmonicResidue q a A B - primePoolHarmonicMass A B / q.totient =
      ∑ p ∈ Finset.Ico A B, inversePrimeLogWeight p * primeResidueLogCoefficient q a p := by
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  unfold primeHarmonicResidue primePoolHarmonicMass
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  unfold primePool
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hlog := hp.log_ne_zero
    by_cases hpa : p % q = a
    · simp only [if_pos hp, inversePrimeLogWeight, primeResidueLogCoefficient, if_pos hpa]
      field_simp
    · simp only [if_pos hp, inversePrimeLogWeight, primeResidueLogCoefficient, if_neg hpa]
      field_simp
      ring
  · simp [hp, primeResidueLogCoefficient]

theorem primeHarmonicResidue_error_of_prefix_bound {q A B : ℕ} (a : ℕ)
    (hq : 1 ≤ q) (hA : 2 ≤ A) (hAB : A < B) {T : ℝ}
    (hf : ∀ n ∈ Finset.Icc A B,
      |∑ p ∈ Finset.range n, primeResidueLogCoefficient q a p| ≤ T) :
    |primeHarmonicResidue q a A B - primePoolHarmonicMass A B / q.totient| ≤
      2 * T / ((A : ℝ) * Real.log A) := by
  rw [primeHarmonicResidue_defect_weighted q a A B hq]
  have hb := weighted_sum_abs_le_prefix_bound
    (primeResidueLogCoefficient q a) inversePrimeLogWeight hAB
    (fun i hi => (inversePrimeLogWeight_pos (hA.trans (Finset.mem_Icc.mp hi).1)).le)
    (fun i hi => inversePrimeLogWeight_antitone
      (hA.trans (Finset.mem_Ico.mp hi).1) (by omega)) hf
  simpa only [inversePrimeLogWeight, div_eq_mul_inv, mul_one, one_mul] using hb

theorem primeHarmonicResidue_dyadic_error {q A : ℕ} (a : ℕ)
    (hq : 1 ≤ q) (hA : 2 ≤ A) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ n ∈ Finset.Icc A (2 * A),
      |∑ p ∈ Finset.range n, primeResidueLogCoefficient q a p| ≤ ε * n) :
    |primeHarmonicResidue q a A (2 * A) - primePoolHarmonicMass A (2 * A) / q.totient| ≤
      4 * ε / Real.log A := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hb := primeHarmonicResidue_error_of_prefix_bound a hq hA (by omega : A < 2 * A)
    (T := ε * (2 * A : ℕ)) (fun n hn => (hf n hn).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hε))
  have he : 2 * (ε * (2 * A : ℕ)) / ((A : ℝ) * Real.log A) = 4 * ε / Real.log A := by
    push_cast
    field_simp
    ring
  rwa [he] at hb

end Hindman168
