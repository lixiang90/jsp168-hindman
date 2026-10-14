import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The sharp one-residue-class harmonic estimate

A progression with positive step `q` starts at its first point `s` in
`[A,A+q]` and contains precisely its first `n` points in `[A,B)`.
The harmonic sum differs from `log(B/A)/q` by at most `1/A`.
This is the analytic ingredient of the paper's periodic-harmonic estimate;
the coprime-residue partition and its cardinality are separate inputs.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def progressionHarmonic (s q : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (s + q * j)⁻¹

theorem affine_inv_antitone {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (n : ℕ) :
    AntitoneOn (fun x : ℝ => (s + q * x)⁻¹) (Set.Icc 0 (n : ℝ)) := by
  intro x hx y _ hxy
  apply inv_anti₀
  · nlinarith [hx.1]
  · nlinarith

theorem integral_affine_inv {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (n : ℕ) :
    (∫ x in (0 : ℝ)..(n : ℝ), (s + q * x)⁻¹) =
      Real.log ((s + q * n) / s) / q := by
  have ht : 0 < s + q * n := by
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  rw [intervalIntegral.integral_comp_add_mul (fun x : ℝ => x⁻¹) hq.ne' s]
  simp only [mul_zero, add_zero, smul_eq_mul]
  rw [integral_inv_of_pos hs ht]
  ring

theorem progression_integral_le {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (n : ℕ) :
    Real.log ((s + q * n) / s) / q ≤ progressionHarmonic s q n := by
  have ha : AntitoneOn (fun x : ℝ => (s + q * x)⁻¹) (Set.Icc 0 (0 + (n : ℝ))) := by
    simpa only [zero_add] using affine_inv_antitone hs hq n
  have h := ha.integral_le_sum
  simpa only [zero_add, integral_affine_inv hs hq n, progressionHarmonic] using h

theorem progression_sum_le {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (n : ℕ) :
    progressionHarmonic s q (n + 1) ≤ s⁻¹ + Real.log ((s + q * n) / s) / q := by
  have ha : AntitoneOn (fun x : ℝ => (s + q * x)⁻¹) (Set.Icc 0 (0 + (n : ℝ))) := by
    simpa only [zero_add] using affine_inv_antitone hs hq n
  have h := ha.sum_le_integral
  simp only [zero_add, integral_affine_inv hs hq n] at h
  have he : progressionHarmonic s q (n + 1) =
      s⁻¹ + ∑ j ∈ Finset.range n, (s + q * (j + 1 : ℕ))⁻¹ := by
    simp [progressionHarmonic, Finset.sum_range_succ', add_comm]
  rw [he]
  linarith

/-- A sharp estimate valid even when the half-open interval contains no
point of this residue class (`n = 0`). Endpoint gaps cost only `1/A`. -/
theorem progression_harmonic_error {A B s q : ℝ} (n : ℕ)
    (hA : 0 < A) (hAB : A < B) (hq : 0 < q)
    (hAs : A ≤ s) (hsAq : s ≤ A + q)
    (hcover : B ≤ s + q * n)
    (hpoints : ∀ j < n, s + q * j < B) :
    |progressionHarmonic s q n - Real.log (B / A) / q| ≤ A⁻¹ := by
  have hs : 0 < s := hA.trans_le hAs
  have hB : 0 < B := hA.trans hAB
  have ht : 0 < s + q * n := hB.trans_le hcover
  have hgap : Real.log (s / A) ≤ q / A := by
    calc
      Real.log (s / A) ≤ s / A - 1 := Real.log_le_sub_one_of_pos (div_pos hs hA)
      _ = (s - A) / A := by field_simp
      _ ≤ q / A := div_le_div_of_nonneg_right (by linarith) hA.le
  have hmain : Real.log (B / A) ≤ Real.log ((s + q * n) / s) + q / A := by
    rw [Real.log_div hB.ne' hA.ne', Real.log_div ht.ne' hs.ne']
    rw [Real.log_div hs.ne' hA.ne'] at hgap
    have hlog := Real.log_le_log hB hcover
    linarith
  have hlower : Real.log (B / A) / q ≤ progressionHarmonic s q n + A⁻¹ := by
    apply (div_le_iff₀ hq).mpr
    have hlow := (div_le_iff₀ hq).mp (progression_integral_le hs hq n)
    rw [show q / A = q * A⁻¹ from div_eq_mul_inv q A] at hmain
    nlinarith
  have hupper : progressionHarmonic s q n ≤ Real.log (B / A) / q + A⁻¹ := by
    cases n with
    | zero =>
      have hlog : 0 ≤ Real.log (B / A) :=
        Real.log_nonneg ((le_div_iff₀ hA).mpr (by linarith))
      have hd := div_nonneg hlog hq.le
      have hi := inv_nonneg.mpr hA.le
      simp only [progressionHarmonic, Finset.range_zero, Finset.sum_empty]
      linarith
    | succ n =>
      have hp : s + q * n < B := hpoints n (Nat.lt_succ_self n)
      have ht' : 0 < s + q * n := by
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hlogs : Real.log ((s + q * n) / s) ≤ Real.log (B / A) := by
        rw [Real.log_div ht'.ne' hs.ne', Real.log_div hB.ne' hA.ne']
        have h1 := Real.log_le_log ht' hp.le
        have h2 := Real.log_le_log hA hAs
        linarith
      have hd := div_le_div_of_nonneg_right hlogs hq.le
      have hi := inv_anti₀ hA hAs
      have hu := progression_sum_le hs hq n
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Hindman168
