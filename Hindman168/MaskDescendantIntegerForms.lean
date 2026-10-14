import Hindman168.MaskFreshTupleEvaluations

/-! The actual flattened descendant integer forms are the retained old
form or exactly one of the two absorbed coordinate branches. Natural
coefficient quotients use the unchanged maximum-support anchor. -/

namespace Hindman168

open scoped BigOperators Classical

variable {n r m : ℕ}

noncomputable def maskFreshCoordinates (y : Bool → ℕ) (b : Bool)
    (tag : Fin (m + 1) → Fin 3) (z : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ :=
  fun j => (maskFreshScalar y b (tag j) : ℤ) * z j

namespace MaskColumnPlan

variable {S U : Finset (Fin (m + 1))}

def freshValues (P : MaskColumnPlan S U) (p q : ℕ) (b : Bool) : ℕ :=
  match P with
  | .outside _ _ _ => if b then q else p
  | .balanced _ _ _ _ _ _ _ => if b then p else q

noncomputable def branchCoordinates (P : MaskColumnPlan S U) (p q : ℕ) (b : Bool)
    (z : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ :=
  if b then P.absorbedCoordinates q p z else P.absorbedCoordinates p q z

theorem freshCoordinates_eq_branch (P : MaskColumnPlan S U) (p q : ℕ) (b : Bool)
    (z : Fin (m + 1) → ℤ) :
    maskFreshCoordinates (P.freshValues p q) b P.tag z = P.branchCoordinates p q b z := by
  cases P with
  | outside u hu hU =>
    cases b <;> funext j
    all_goals by_cases hj : j = u
    all_goals simp [maskFreshCoordinates, maskFreshScalar, freshValues, branchCoordinates,
      absorbedCoordinates, tag, hj]
  | balanced u v hu hv huU hvU hne =>
    cases b <;> funext j
    all_goals by_cases hj : j = u
    all_goals by_cases hv' : j = v
    all_goals simp [maskFreshCoordinates, maskFreshScalar, freshValues, branchCoordinates,
      absorbedCoordinates, tag, maskAbsorbedCoordinates, hj, hv', hne, Ne.symm hne]

end MaskColumnPlan

theorem PolynomialRowFamily.flattenedMaskStep_integerRow_evaluated
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag)
    (x : Fin n → ℕ) (y : Bool → ℕ) (c : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    (F.flattenedMaskStep tag).normalizedIntegerRow (maskFreshTuple x y) c (Fintype.equivFin _ d) j =
      F.normalizedIntegerRow x c d.val.1 j *
        (d.val.2.elim 1 (fun b => maskFreshScalar y b (tag j)) : ℤ) := by
  unfold PolynomialRowFamily.normalizedIntegerRow
  rw [F.flattenedMaskStep_normalizationAnchor tag d, maskFreshTuple_eval_descendantRow]
  ring

theorem PolynomialRowFamily.flattenedMaskStep_integerForm_evaluated
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag)
    (x : Fin n → ℕ) (y : Bool → ℕ) (c : Fin (m + 1) → ℕ) (z : Fin (m + 1) → ℤ) :
    (F.flattenedMaskStep tag).normalizedIntegerLinearForm (maskFreshTuple x y) c (Fintype.equivFin _ d) z =
      F.normalizedIntegerLinearForm x c d.val.1
        (fun j => (d.val.2.elim 1 (fun b => maskFreshScalar y b (tag j)) : ℤ) * z j) := by
  unfold PolynomialRowFamily.normalizedIntegerLinearForm
  apply Finset.sum_congr rfl
  intro j _
  rw [F.flattenedMaskStep_integerRow_evaluated]
  ring

theorem PolynomialRowFamily.flattenedMaskStep_integerForm_none
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag) (hd : d.val.2 = none)
    (x : Fin n → ℕ) (y : Bool → ℕ) (c : Fin (m + 1) → ℕ) (z : Fin (m + 1) → ℤ) :
    (F.flattenedMaskStep tag).normalizedIntegerLinearForm (maskFreshTuple x y) c (Fintype.equivFin _ d) z =
      F.normalizedIntegerLinearForm x c d.val.1 z := by
  simpa only [hd, Option.elim_none, Nat.cast_one, one_mul] using
    F.flattenedMaskStep_integerForm_evaluated tag d x y c z

theorem PolynomialRowFamily.flattenedMaskStep_integerForm_branch
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U)
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (d : MaskDescendant F P.tag) (b : Bool) (hd : d.val.2 = some b)
    (x : Fin n → ℕ) (p q : ℕ) (c : Fin (m + 1) → ℕ) (z : Fin (m + 1) → ℤ) :
    (F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
      (maskFreshTuple x (P.freshValues p q)) c (Fintype.equivFin _ d) z =
      F.normalizedIntegerLinearForm x c d.val.1 (P.branchCoordinates p q b z) := by
  rw [F.flattenedMaskStep_integerForm_evaluated]
  simp only [hd, Option.elim_some]
  exact congrArg (F.normalizedIntegerLinearForm x c d.val.1)
    (P.freshCoordinates_eq_branch p q b z)

theorem PolynomialRowFamily.flattenedMaskStep_integerForm_plan
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U)
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (d : MaskDescendant F P.tag) (x : Fin n → ℕ) (p q : ℕ)
    (c : Fin (m + 1) → ℕ) (z : Fin (m + 1) → ℤ) :
    (F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
      (maskFreshTuple x (P.freshValues p q)) c (Fintype.equivFin _ d) z =
      d.val.2.elim (F.normalizedIntegerLinearForm x c d.val.1 z)
        (fun b => F.normalizedIntegerLinearForm x c d.val.1 (P.branchCoordinates p q b z)) := by
  cases hd : d.val.2 with
  | none => simpa only [hd, Option.elim_none] using F.flattenedMaskStep_integerForm_none P.tag d hd x _ c z
  | some b => simpa only [hd, Option.elim_some] using F.flattenedMaskStep_integerForm_branch P d b hd x p q c z

end Hindman168
