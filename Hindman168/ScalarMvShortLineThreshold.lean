import Mathlib.Tactic

namespace Hindman168

/-- One original-length threshold, fixed before N, makes the ACTUAL quotient
length long enough and preserves the true original scale within 2*L^2. -/
theorem scalar_mv_short_line_threshold (L B A : ℕ) (hL : 0 < L)
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ T : ℕ, 0 < T ∧ ∀ N : ℕ, T ≤ N →
      B ≤ N ∧ L^2 ≤ N ∧ 0 < N/L^2 ∧ (A : ℝ)/(N/L^2 : ℕ) ≤ μ/10 ∧
        N ≤ 2*L^2*(N/L^2) := by
  let W := ⌈10*(A : ℝ)/μ⌉₊+1
  let T := L^2*(B+W+1)
  have hW : 0 < W := by dsimp only [W]; omega
  have hL2 : 0 < L^2 := by positivity
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨T, hT, ?_⟩
  intro N hTN
  have hdiv : B+W+1 ≤ N/L^2 := (Nat.le_div_iff_mul_le hL2).mpr (by
    simpa only [T, mul_comm] using hTN)
  have hH : 0 < N/L^2 := by omega
  have hBN : B ≤ N := (by omega : B ≤ N/L^2).trans (Nat.div_le_self _ _)
  have hLN : L^2 ≤ N := by
    simpa only [one_mul] using (Nat.le_div_iff_mul_le hL2).mp (by omega : 1 ≤ N/L^2)
  have hHr : (0 : ℝ) < (N/L^2 : ℕ) := by exact_mod_cast hH
  have hWbound : 10*(A : ℝ)/μ ≤ W := (Nat.le_ceil _).trans (by
    dsimp only [W]
    push_cast
    linarith)
  have hWH : (W : ℝ) ≤ (N/L^2 : ℕ) := by exact_mod_cast (by omega : W ≤ N/L^2)
  have htol : (A : ℝ)/(N/L^2 : ℕ) ≤ μ/10 := by
    apply (div_le_iff₀ hHr).mpr
    have h := (div_le_iff₀ hμ).mp (hWbound.trans hWH)
    nlinarith
  have hmod := Nat.mod_lt N hL2
  have heq := Nat.div_add_mod N (L^2)
  have htwo : N ≤ 2*L^2*(N/L^2) := by nlinarith
  exact ⟨hBN, hLN, hH, htol, htwo⟩

end Hindman168
