import Hindman168.MaskInitialCenteredCorrelation

/-! The original initial integer rows are exactly the nonempty subset
sums, normalized at the maximum element of that subset. These identities
hold before any asymptotic coefficient conditions are used. -/

namespace Hindman168

open scoped BigOperators Classical

variable {m n : ℕ}

theorem initialMaskRowFamily_support (U : NonemptyColumnSubset (m+1)) :
    (initialMaskRowFamily (R := MvPolynomial (Fin n) ℤ) m).support
      (initialMaskRowIndex U.val U.property) = U.val := by
  ext k
  simp only [PolynomialRowFamily.support, Finset.mem_filter, Finset.mem_univ, true_and,
    initialMaskRowFamily_row, columnSubsetIndicator_nonzero_iff]

theorem initialMaskRowFamily_normalizationAnchor (U : NonemptyColumnSubset (m+1)) :
    (initialMaskRowFamily (R := MvPolynomial (Fin n) ℤ) m).normalizationAnchor
      (initialMaskRowIndex U.val U.property) = U.val.max' U.property := by
  apply le_antisymm
  · apply U.val.le_max'
    have h := (initialMaskRowFamily (R := MvPolynomial (Fin n) ℤ) m).normalizationAnchor_ne_zero
      (initialMaskRowIndex U.val U.property)
    rw [initialMaskRowFamily_row] at h
    exact (columnSubsetIndicator_nonzero_iff _ _).mp h
  · apply (initialMaskRowFamily (R := MvPolynomial (Fin n) ℤ) m).le_normalizationAnchor
    rw [initialMaskRowFamily_row]
    exact (columnSubsetIndicator_nonzero_iff _ _).mpr (Finset.max'_mem _ _)

noncomputable def maskSubsetIntegerForm (c : Fin (m+1) → ℕ)
    (U : NonemptyColumnSubset (m+1)) (z : Fin (m+1) → ℤ) : ℤ :=
  ∑ k ∈ U.val, ((c k / c (U.val.max' U.property) : ℕ) : ℤ) * z k

theorem initialMaskRowFamily_integerForm (x : Fin n → ℕ) (c : Fin (m+1) → ℕ)
    (U : NonemptyColumnSubset (m+1)) (z : Fin (m+1) → ℤ) :
    (initialMaskRowFamily (R := MvPolynomial (Fin n) ℤ) m).normalizedIntegerLinearForm x c
      (initialMaskRowIndex U.val U.property) z = maskSubsetIntegerForm c U z := by
  unfold PolynomialRowFamily.normalizedIntegerLinearForm PolynomialRowFamily.normalizedIntegerRow
  rw [initialMaskRowFamily_normalizationAnchor]
  simp [initialMaskRowFamily_row, columnSubsetIndicator, maskSubsetIntegerForm,
    Finset.sum_ite_mem]

theorem initialMaskRowFamily_integerProduct (c : Fin (m+1) → ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (x : Fin n → ℕ) (z : Fin (m+1) → ℤ) :
    maskRowFunctionProduct (initialMaskRowFamily (R := MvPolynomial (Fin n) ℤ) m) c
      (fun _ i => f ((Fintype.equivFin (NonemptyColumnSubset (m+1))).symm i)) x z =
      ∏ U : NonemptyColumnSubset (m+1), f U (maskSubsetIntegerForm c U z) := by
  unfold maskRowFunctionProduct
  symm
  apply Fintype.prod_equiv (Fintype.equivFin (NonemptyColumnSubset (m+1)))
  intro U
  dsimp only
  rw [Equiv.symm_apply_apply]
  exact congrArg (f U) (initialMaskRowFamily_integerForm x c U z).symm

end Hindman168
