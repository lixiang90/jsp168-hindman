import Hindman168.MaskDescendantBoundedFunctions

/-! Genuine functions of the new flattened prime tuple recover the
shared old tuple, select the original two fresh primes, and assign the
merged or unchanged function to each actual next-stage row. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

namespace MaskColumnPlan

variable {m : ℕ} {S U : Finset (Fin (m + 1))}

def freshPair (P : MaskColumnPlan S U) (y : Bool → ℕ) : ℕ × ℕ :=
  match P with
  | .outside _ _ _ => (y false, y true)
  | .balanced _ _ _ _ _ _ _ => (y true, y false)

theorem freshPair_values (P : MaskColumnPlan S U) (p q : ℕ) :
    P.freshPair (P.freshValues p q) = (p, q) := by
  cases P <;> rfl

theorem freshValues_pair (P : MaskColumnPlan S U) (y : Bool → ℕ) :
    P.freshValues (P.freshPair y).1 (P.freshPair y).2 = y := by
  cases P <;> funext b <;> cases b <;> rfl

end MaskColumnPlan

variable {m N n r : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))

noncomputable def maskUpdatedRowFunctions {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w : ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (ξ : Fin (2 + n) → ℕ)
    (i : Fin (Fintype.card (MaskDescendant F P.tag))) (t : ℤ) : ℝ :=
  let x := maskFreshOldTuple ξ
  let pq := P.freshPair (maskFreshNewTuple ξ)
  maskDescendantFunction gap C P F w pq.1 pq.2 (f x)
    ((Fintype.equivFin (MaskDescendant F P.tag)).symm i) t

theorem maskUpdatedRowFunctions_join {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w : ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (p q : ℕ)
    (d : MaskDescendant F P.tag) (t : ℤ) :
    maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q))
      (Fintype.equivFin _ d) t = maskDescendantFunction gap C P F w p q (f x) d t := by
  simp only [maskUpdatedRowFunctions, maskFreshOldTuple_join, maskFreshNewTuple_join,
    MaskColumnPlan.freshPair_values, Equiv.symm_apply_apply]

theorem maskUpdatedRowFunctions_evaluated_none {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w : ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (p q : ℕ)
    (d : MaskDescendant F P.tag) (hd : d.val.2 = none)
    (c : Fin (m + 1) → ℕ) (z : Fin (m + 1) → ℤ) :
    maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q)) (Fintype.equivFin _ d)
      ((F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
        (maskFreshTuple x (P.freshValues p q)) c (Fintype.equivFin _ d) z) =
      divisorWeightedMerge (maskFamilyRowDivisorMass gap C F w d.val.1)
        (P.absorbedScalar p q (P.tag (F.normalizationAnchor d.val.1)))
        (P.absorbedScalar q p (P.tag (F.normalizationAnchor d.val.1)))
        (f x d.val.1) (f x d.val.1) (F.normalizedIntegerLinearForm x c d.val.1 z) := by
  rw [maskUpdatedRowFunctions_join, maskDescendantFunction_none gap C P F w p q (f x) d hd,
    F.flattenedMaskStep_integerForm_none P.tag d hd]

theorem maskUpdatedRowFunctions_evaluated_branch {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w : ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (p q : ℕ)
    (d : MaskDescendant F P.tag) (b : Bool) (hd : d.val.2 = some b)
    (c : Fin (m + 1) → ℕ) (z : Fin (m + 1) → ℤ) :
    maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q)) (Fintype.equivFin _ d)
      ((F.flattenedMaskStep P.tag).normalizedIntegerLinearForm
        (maskFreshTuple x (P.freshValues p q)) c (Fintype.equivFin _ d) z) =
      f x d.val.1 (F.normalizedIntegerLinearForm x c d.val.1 (P.branchCoordinates p q b z)) := by
  rw [maskUpdatedRowFunctions_join, maskDescendantFunction_some gap C P F w p q (f x) d b hd,
    F.flattenedMaskStep_integerForm_branch P d b hd]

theorem maskUpdatedRowFunctions_tracked {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w : ℕ) (f : (Fin n → ℕ) → Fin r → ℤ → ℝ) (x : Fin n → ℕ) (p q : ℕ)
    (i : Fin r) (hi : ¬ maskRowInvariant (F.row i) P.tag) (b : Bool) (t : ℤ) :
    maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q))
      (maskTrackedRowIndex F P.tag i hi b) t = f x i t := by
  unfold maskTrackedRowIndex
  rw [maskUpdatedRowFunctions_join]
  exact maskDescendantFunction_some gap C P F w p q (f x)
    (maskNoninvariantCopy F P.tag i hi b) b rfl t

variable (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskUpdatedRowFunctions_eventually_join_bound :
    ∀ᶠ w in atTop, ∀ (n r : ℕ)
      (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
      (S U : Finset (Fin (m + 1))) (P : MaskColumnPlan S U),
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f : (Fin n → ℕ) → Fin r → ℤ → ℝ, ∀ x,
      (∀ i t, |f x i t| ≤ maskFamilyRowMajorant gap C F w i t) → ∀ i t,
      |maskUpdatedRowFunctions gap C P F w f (maskFreshTuple x (P.freshValues p q)) i t| ≤
        maskFamilyRowMajorant gap C (F.flattenedMaskStep P.tag) w i t := by
  filter_upwards [maskDescendantFunction_eventually_bound gap C hC htail] with w hw
  intro n r F S U P p hp q hq f x hf i t
  let d := (Fintype.equivFin (MaskDescendant F P.tag)).symm i
  have he := maskUpdatedRowFunctions_join gap C P F w f x p q d t
  simp only [d, Equiv.apply_symm_apply] at he
  rw [he]
  simpa only [d, Equiv.apply_symm_apply] using hw n r F S U P p hp q hq (f x) hf d t

include hC htail in
theorem maskStageUpdatedRowFunctions_eventually_bound
    (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x,
      (∀ i t, |f x i t| ≤ maskStageRowMajorant S hS gap C k w i t) →
      ∀ i : Fin ((maskPrefixRowStage S hS k).step hS U).rowCount, ∀ t,
      |maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS)
        (maskPrefixRowStage S hS k).rows w f
        (maskFreshTuple x ((chosenMaskColumnPlan S U hS).freshValues p q)) i t| ≤
      maskFamilyRowMajorant gap C ((maskPrefixRowStage S hS k).step hS U).rows w i t := by
  filter_upwards [maskUpdatedRowFunctions_eventually_join_bound gap C hC htail] with w hw
  intro k U p hp q hq f x hf i t
  exact hw _ _ (maskPrefixRowStage S hS k).rows S U (chosenMaskColumnPlan S U hS)
    p hp q hq f x hf i t

end Hindman168
