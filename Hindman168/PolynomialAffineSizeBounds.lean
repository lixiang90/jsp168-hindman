import Hindman168.PolynomialAffineRootSplit
import Hindman168.PolynomialTranslationSizeBounds
import Hindman168.PredictionQuotientLengths

/-! Fixed polynomial budgets for normalized coefficients and affine offsets.
Columns above the maximum support anchor vanish, so their sample size is irrelevant. -/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

noncomputable def rowValueSizeExponent
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (i : Fin r) : ℕ :=
  Finset.univ.sup (fun k : Fin (m + 1) => integerPolynomialCoeffSize (F.row i k) + (F.row i k).totalDegree)

theorem rowValueSizeExponent_entry_le
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (i : Fin r) (k : Fin (m + 1)) :
    integerPolynomialCoeffSize (F.row i k) + (F.row i k).totalDegree ≤ F.rowValueSizeExponent i :=
  by
    exact Finset.le_sup (f := fun k => integerPolynomialCoeffSize (F.row i k) + (F.row i k).totalDegree) (Finset.mem_univ k)

theorem normalizedIntegerRow_size_bound
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r) (k : Fin (m + 1)) {B L : ℕ}
    (hB : 2 ≤ B) (hx : ∀ j, x j ≤ B) (hc : c k ≤ L) :
    (F.normalizedIntegerRow x c i k).natAbs ≤ L * B ^ F.rowValueSizeExponent i := by
  unfold normalizedIntegerRow
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  apply Nat.mul_le_mul ((Nat.div_le_self _ _).trans hc)
  exact (integerPolynomial_eval_fixed_power_cap (F.row i k) x hB hx).trans
    (Nat.pow_le_pow_right (by omega) (F.rowValueSizeExponent_entry_le i k))

theorem translationModulus_size_bound
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (x : Fin n → ℕ) (i : Fin r) {B L : ℕ}
    (hB : 2 ≤ B) (hx : ∀ j, x j ≤ B) (hM : (master.modulus w : ℕ) ≤ L) :
    F.translationModulus master w x i ≤ L *
      B ^ (integerPolynomialCoeffSize (F.denominator i) + (F.denominator i).totalDegree) := by
  unfold translationModulus
  apply Nat.mul_le_mul hM
  exact (roughPartNat_le_value _ _).trans
    (integerPolynomial_eval_fixed_power_cap (F.denominator i) x hB hx)

theorem normalizedRootOffset_size_bound
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (rest : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i} → ℤ) {B L Z : ℕ}
    (hB : 2 ≤ B) (hx : ∀ j, x j ≤ B) (hc : ∀ k, c k ≤ L)
    (hz : ∀ k, k.val < F.normalizationAnchor i → (rest k).natAbs ≤ Z) :
    (F.normalizedRootOffset x c i rest).natAbs ≤ (m + 1) * (L * B ^ F.rowValueSizeExponent i * Z) := by
  unfold normalizedRootOffset
  calc
    _ ≤ ∑ k : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i},
        (F.normalizedIntegerRow x c i k.val * rest k).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i},
        L * B ^ F.rowValueSizeExponent i * Z := by
      apply Finset.sum_le_sum
      intro k _
      rcases lt_or_gt_of_ne k.property with hlt | hgt
      · rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (F.normalizedIntegerRow_size_bound x c i k.val hB hx (hc _)) (hz k hlt)
      · rw [F.normalizedIntegerRow_above_anchor x c i k.val hgt, zero_mul, Int.natAbs_zero]
        exact Nat.zero_le _
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ]
      change Fintype.card {k : Fin (m + 1) // k ≠ F.normalizationAnchor i} *
        (L * B ^ F.rowValueSizeExponent i * Z) ≤ _
      apply Nat.mul_le_mul_right _
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        (fun k : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i} => k.val) Subtype.val_injective

end Hindman168.PolynomialRowFamily
