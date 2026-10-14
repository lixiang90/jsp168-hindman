import Hindman168.MaskDescendantProductSplit

/-! Whole row products for the actual flattened update. The old tuple
is shared by both noninvariant branches, while each invariant row
contributes exactly one divisor-weighted merged function. -/

namespace Hindman168

open scoped BigOperators Classical

variable {m N n r : ℕ}

noncomputable def maskRowFunctionProduct
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (c : Fin (m + 1) → ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ)
    (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i, f x i (F.normalizedIntegerLinearForm x c i z)

noncomputable def maskInvariantFunctionProduct
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (c : Fin (m + 1) → ℕ)
    (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i : MaskInvariantRowIndex F tag, f x i.val (F.normalizedIntegerLinearForm x c i.val z)

noncomputable def maskNoninvariantFunctionProduct
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (c : Fin (m + 1) → ℕ)
    (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i : MaskNoninvariantRowIndex F tag, f x i.val (F.normalizedIntegerLinearForm x c i.val z)

theorem maskRowFunctionProduct_split
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (c : Fin (m + 1) → ℕ)
    (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) :
    maskRowFunctionProduct F c f x z = maskInvariantFunctionProduct F tag c f x z *
      maskNoninvariantFunctionProduct F tag c f x z := by
  unfold maskRowFunctionProduct maskInvariantFunctionProduct maskNoninvariantFunctionProduct
  have hi := Finset.prod_subtype (p := fun i => maskRowInvariant (F.row i) tag)
    (F := (inferInstance : Fintype (MaskInvariantRowIndex F tag)))
    (Finset.univ.filter (fun i => maskRowInvariant (F.row i) tag))
    (by intro i; simp) (fun i => f x i (F.normalizedIntegerLinearForm x c i z))
  have hn := Finset.prod_subtype (p := fun i => ¬ maskRowInvariant (F.row i) tag)
    (F := (inferInstance : Fintype (MaskNoninvariantRowIndex F tag)))
    (Finset.univ.filter (fun i => ¬ maskRowInvariant (F.row i) tag))
    (by intro i; simp) (fun i => f x i (F.normalizedIntegerLinearForm x c i z))
  rw [← hi, ← hn]
  exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm

variable (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))

noncomputable def maskMergedFunctionProduct {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (c : Fin (m + 1) → ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ)
    (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i : MaskInvariantRowIndex F P.tag,
    divisorWeightedMerge (maskFamilyRowDivisorMass gap C F w i.val)
      (P.absorbedScalar p q (P.tag (F.normalizationAnchor i.val)))
      (P.absorbedScalar q p (P.tag (F.normalizationAnchor i.val)))
      (f x i.val) (f x i.val) (F.normalizedIntegerLinearForm x c i.val z)

theorem maskUpdatedRowProducts_descendants {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (c : Fin (m + 1) → ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ)
    (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) :
    maskRowFunctionProduct (F.flattenedMaskStep P.tag) c (maskUpdatedRowFunctions gap C P F w f)
      (maskFreshTuple x (P.freshValues p q)) z =
    ∏ d : MaskDescendant F P.tag,
      maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q))
        (Fintype.equivFin _ d)
        ((F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
          (maskFreshTuple x (P.freshValues p q)) c (Fintype.equivFin _ d) z) := by
  unfold maskRowFunctionProduct
  apply Fintype.prod_equiv (Fintype.equivFin (MaskDescendant F P.tag)).symm
  intro i
  simp only [Equiv.apply_symm_apply]

theorem maskUpdatedRowProducts_join {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (c : Fin (m + 1) → ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ)
    (x : Fin n → ℕ) (z : Fin (m + 1) → ℤ) :
    maskRowFunctionProduct (F.flattenedMaskStep P.tag) c (maskUpdatedRowFunctions gap C P F w f)
      (maskFreshTuple x (P.freshValues p q)) z =
      maskMergedFunctionProduct gap C P F w p q c f x z *
        maskNoninvariantFunctionProduct F P.tag c f x (P.absorbedCoordinates p q z) *
        maskNoninvariantFunctionProduct F P.tag c f x (P.absorbedCoordinates q p z) := by
  rw [maskUpdatedRowProducts_descendants, maskDescendant_product_split]
  have hi : (∏ i : MaskInvariantRowIndex F P.tag,
      maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q))
        (Fintype.equivFin _ (maskInvariantCopy F P.tag i.val i.property))
        ((F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
          (maskFreshTuple x (P.freshValues p q)) c
          (Fintype.equivFin _ (maskInvariantCopy F P.tag i.val i.property)) z)) =
      maskMergedFunctionProduct gap C P F w p q c f x z := by
    unfold maskMergedFunctionProduct
    apply Finset.prod_congr rfl
    intro i _
    exact maskUpdatedRowFunctions_evaluated_none gap C P F w f x p q
      (maskInvariantCopy F P.tag i.val i.property) rfl c z
  rw [hi]
  have hn : (∏ i : MaskNoninvariantRowIndex F P.tag,
      maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q))
        (Fintype.equivFin _ (maskNoninvariantCopy F P.tag i.val i.property false))
        ((F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
          (maskFreshTuple x (P.freshValues p q)) c
          (Fintype.equivFin _ (maskNoninvariantCopy F P.tag i.val i.property false)) z) *
      maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q))
        (Fintype.equivFin _ (maskNoninvariantCopy F P.tag i.val i.property true))
        ((F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
          (maskFreshTuple x (P.freshValues p q)) c
          (Fintype.equivFin _ (maskNoninvariantCopy F P.tag i.val i.property true)) z)) =
      maskNoninvariantFunctionProduct F P.tag c f x (P.absorbedCoordinates p q z) *
      maskNoninvariantFunctionProduct F P.tag c f x (P.absorbedCoordinates q p z) := by
    unfold maskNoninvariantFunctionProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [maskUpdatedRowFunctions_evaluated_branch gap C P F w f x p q
      (maskNoninvariantCopy F P.tag i.val i.property false) false rfl,
      maskUpdatedRowFunctions_evaluated_branch gap C P F w f x p q
      (maskNoninvariantCopy F P.tag i.val i.property true) true rfl]
    rfl
  rw [hn, mul_assoc]

end Hindman168
