import Hindman168.MaskGeneratedNormalizedIntegerRows
import Hindman168.FinitePivotCoordinates

/-! Split the maximum-support harmonic coordinate from the normalized form.
The remaining integer offset is divisible by the actual primorial. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem CoefficientOneMonomial.eval_nonneg {σ : Type*} {P : MvPolynomial σ ℤ}
    (hP : CoefficientOneMonomial P) (x : σ → ℕ) :
    0 ≤ MvPolynomial.eval (fun j => (x j : ℤ)) P := by
  obtain ⟨e, rfl⟩ := hP
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  exact Finset.prod_nonneg (fun j _ => pow_nonneg (Nat.cast_nonneg (x j)) _)

theorem CoefficientOneMonomial.eval_eq_natAbs {σ : Type*} {P : MvPolynomial σ ℤ}
    (hP : CoefficientOneMonomial P) (x : σ → ℕ) :
    MvPolynomial.eval (fun j => (x j : ℤ)) P =
      ((MvPolynomial.eval (fun j => (x j : ℤ)) P).natAbs : ℤ) := by
  rw [Int.natCast_natAbs, abs_of_nonneg (hP.eval_nonneg x)]

namespace PolynomialRowFamily

variable {n r m : ℕ}

noncomputable def normalizedRootOffset
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (rest : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i} → ℤ) : ℤ :=
  ∑ k, F.normalizedIntegerRow x c i k.val * rest k

theorem normalizedIntegerLinearForm_pivot
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (rest : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i} → ℤ) (y : ℤ) :
    F.normalizedIntegerLinearForm x c i (insertPivotCoordinate (F.normalizationAnchor i) rest y) =
      F.normalizedIntegerRow x c i (F.normalizationAnchor i) * y + F.normalizedRootOffset x c i rest := by
  unfold normalizedIntegerLinearForm normalizedRootOffset
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (F.normalizationAnchor i), insertPivotCoordinate_self]
  congr 1
  apply Fintype.sum_congr
  intro k
  rw [congrFun (insertPivotCoordinate_rest (F.normalizationAnchor i) rest y) k]

theorem NormalizedIntegerRowConditions.rootOffset_W
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {x : Fin n → ℕ} {c : Fin (m + 1) → ℕ} {W : ℕ}
    (hF : F.NormalizedIntegerRowConditions x c W) (i : Fin r)
    (rest : {k : Fin (m + 1) // k ≠ F.normalizationAnchor i} → ℤ) :
    (W : ℤ) ∣ F.normalizedRootOffset x c i rest := by
  unfold normalizedRootOffset
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (hF.off_anchor_W i k.val k.property) (rest k))

end PolynomialRowFamily
end Hindman168
