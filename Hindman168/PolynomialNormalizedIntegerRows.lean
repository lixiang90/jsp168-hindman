import Hindman168.MasterChainColumnRatios

/-!
Integer normalized rows use actual natural coefficient quotients.
The maximum-support anchor removes all columns above it.
-/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

noncomputable def normalizedIntegerRow
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (k : Fin (m + 1)) : ℤ :=
  ((c k / c (F.normalizationAnchor i) : ℕ) : ℤ) *
    MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i k)

noncomputable def normalizedIntegerLinearForm
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (z : Fin (m + 1) → ℤ) : ℤ :=
  ∑ k, F.normalizedIntegerRow x c i k * z k

theorem normalizedIntegerRow_cast
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (hc : 0 < c (F.normalizationAnchor i))
    (hdiv : ∀ k, k ≤ F.normalizationAnchor i → c (F.normalizationAnchor i) ∣ c k)
    (k : Fin (m + 1)) :
    (F.normalizedIntegerRow x c i k : ℚ) =
      ((c k : ℚ) / c (F.normalizationAnchor i)) *
        (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i k) : ℚ) := by
  by_cases hk : F.row i k = 0
  · simp [normalizedIntegerRow, hk]
  · simp only [normalizedIntegerRow, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdiv k (F.le_normalizationAnchor i k hk))
      (by exact_mod_cast hc.ne')]

theorem normalizedIntegerLinearForm_cast
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (hc : 0 < c (F.normalizationAnchor i))
    (hdiv : ∀ k, k ≤ F.normalizationAnchor i → c (F.normalizationAnchor i) ∣ c k)
    (z : Fin (m + 1) → ℤ) :
    (F.normalizedIntegerLinearForm x c i z : ℚ) = F.normalizedLinearForm x c i z := by
  simp only [normalizedIntegerLinearForm, normalizedLinearForm, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl (fun k _ => by rw [F.normalizedIntegerRow_cast x c i hc hdiv k])

theorem normalizedIntegerRow_anchor
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (hc : 0 < c (F.normalizationAnchor i)) :
    F.normalizedIntegerRow x c i (F.normalizationAnchor i) =
      MvPolynomial.eval (fun j => (x j : ℤ)) (F.row i (F.normalizationAnchor i)) := by
  unfold normalizedIntegerRow
  rw [Nat.div_self hc]
  simp

theorem normalizedIntegerRow_above_anchor
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (k : Fin (m + 1)) (hk : F.normalizationAnchor i < k) :
    F.normalizedIntegerRow x c i k = 0 := by
  simp [normalizedIntegerRow, F.row_zero_above_normalizationAnchor i k hk]

theorem normalizedIntegerRow_off_anchor_W_divisible
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (W : ℕ) (i : Fin r)
    (hratio : ∀ k, k < F.normalizationAnchor i → W ∣ c k / c (F.normalizationAnchor i))
    (k : Fin (m + 1)) (hk : k ≠ F.normalizationAnchor i) :
    (W : ℤ) ∣ F.normalizedIntegerRow x c i k := by
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · exact (Int.natCast_dvd_natCast.mpr (hratio k hlt)).trans (dvd_mul_right _ _)
  · rw [F.normalizedIntegerRow_above_anchor x c i k hgt]
    exact dvd_zero _

theorem normalizedIntegerRow_residue_anchor_unit
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (q : ℕ)
    (hc : 0 < c (F.normalizationAnchor i))
    (hu : IsUnit ((MvPolynomial.eval (fun j => (x j : ℤ))
      (F.row i (F.normalizationAnchor i)) : ℤ) : ZMod q)) :
    IsUnit (F.normalizedIntegerRow x c i (F.normalizationAnchor i) : ZMod q) := by
  rwa [F.normalizedIntegerRow_anchor x c i hc]

end Hindman168.PolynomialRowFamily
