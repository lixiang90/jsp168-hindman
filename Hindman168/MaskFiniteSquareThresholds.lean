import Hindman168.MaskOrderedInputPath

/-! Positive tolerances compose a finite noisy squaring chain. This
uses finite eventual thresholds, with no unstated polynomial error
amplification or assumed bound on an intermediate correlation. -/

namespace Hindman168

noncomputable def maskSquareTolerance (c ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | k+1 => maskSquareTolerance c ε k ^ 2 / (c+1)

theorem maskSquareTolerance_pos {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) (k : ℕ) :
    0 < maskSquareTolerance c ε k := by
  induction k with
  | zero => exact hε
  | succ k ih => exact div_pos (pow_pos ih 2) (by linarith)

theorem maskSquareTolerance_succ_shift (c ε : ℝ) (k : ℕ) :
    maskSquareTolerance c ε (k+1) = maskSquareTolerance c (maskSquareTolerance c ε 1) k := by
  induction k with
  | zero => rfl
  | succ k ih => change _ ^ 2 / (c+1) = _ ^ 2 / (c+1); rw [ih]

theorem maskSquareTolerance_closed (c ε : ℝ) (k : ℕ) :
    maskSquareTolerance c ε k = ε ^ (2 ^ k) / (c+1) ^ (2 ^ k - 1) := by
  induction k with
  | zero => simp [maskSquareTolerance]
  | succ k ih =>
    have he : (2 ^ k - 1) * 2 + 1 = 2 ^ (k+1) - 1 := by
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega
    rw [maskSquareTolerance, ih, div_pow, div_div, ← pow_mul ε (2^k) 2,
      ← pow_mul (c+1) (2^k-1) 2, ← pow_succ (c+1) ((2^k-1)*2), he, pow_succ (2 : ℕ) k]

theorem maskSquareTolerance_step (c ε : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    c * maskSquareTolerance c ε (k+1) + maskSquareTolerance c ε (k+1) =
      maskSquareTolerance c ε k ^ 2 := by
  change c * (_ ^ 2 / (c+1)) + _ ^ 2 / (c+1) = _ ^ 2
  have h : c+1 ≠ 0 := by linarith
  field_simp

theorem finite_mask_square_backward {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (q : ℕ) (x : ℕ → ℝ) (hx : ∀ k ≤ q, 0 ≤ x k)
    (hstep : ∀ k < q, x k ^ 2 ≤ c * x (k+1) + maskSquareTolerance c ε (k+1))
    (hend : x q ≤ maskSquareTolerance c ε q) : x 0 ≤ ε := by
  induction q generalizing ε x with
  | zero => simpa only [maskSquareTolerance] using hend
  | succ q ih =>
    have hε' := maskSquareTolerance_pos hc hε 1
    have hfirst : x 1 ≤ maskSquareTolerance c ε 1 := by
      apply ih hε' (fun k => x (k+1))
      · intro k hk; exact hx (k+1) (by omega)
      · intro k hk
        have hs := hstep (k+1) (by omega)
        rw [maskSquareTolerance_succ_shift c ε (k+1)] at hs
        exact hs
      · rw [maskSquareTolerance_succ_shift c ε q] at hend
        exact hend
    have h0 := hstep 0 (by omega)
    have hm := mul_le_mul_of_nonneg_left hfirst hc
    have hidentity := maskSquareTolerance_step c ε hc 0
    have hnonneg := hx 0 (by omega)
    change c * maskSquareTolerance c ε 1 + maskSquareTolerance c ε 1 = ε ^ 2 at hidentity
    nlinarith

end Hindman168
