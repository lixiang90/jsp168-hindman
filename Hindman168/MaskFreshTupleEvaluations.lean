import Hindman168.MaskDescendantNormalization

/-! Exact old/fresh natural prime tuples and evaluation of the already
constructed flattened polynomial coefficients. The old tuple is retained. -/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def maskFreshTuple {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ) :
    Fin (2 + n) → ℕ := fun j => Sum.elim y x ((freshMaskSlotEquiv n).symm j)

noncomputable def maskFreshOldTuple {n : ℕ} (x : Fin (2 + n) → ℕ) : Fin n → ℕ :=
  fun j => x (freshMaskOldSlot n j)

noncomputable def maskFreshNewTuple {n : ℕ} (x : Fin (2 + n) → ℕ) : Bool → ℕ :=
  fun b => x (freshMaskNewSlot n b)

theorem maskFreshTuple_oldSlot {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ) (j : Fin n) :
    maskFreshTuple x y (freshMaskOldSlot n j) = x j := by
  simp [maskFreshTuple, freshMaskOldSlot]

theorem maskFreshTuple_newSlot {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ) (b : Bool) :
    maskFreshTuple x y (freshMaskNewSlot n b) = y b := by
  simp [maskFreshTuple, freshMaskNewSlot]

theorem maskFreshOldTuple_join {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ) :
    maskFreshOldTuple (maskFreshTuple x y) = x := by
  funext j
  exact maskFreshTuple_oldSlot x y j

theorem maskFreshNewTuple_join {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ) :
    maskFreshNewTuple (maskFreshTuple x y) = y := by
  funext b
  exact maskFreshTuple_newSlot x y b

theorem maskFreshTuple_projections {n : ℕ} (x : Fin (2 + n) → ℕ) :
    maskFreshTuple (maskFreshOldTuple x) (maskFreshNewTuple x) = x := by
  funext j
  rw [← (freshMaskSlotEquiv n).apply_symm_apply j]
  cases (freshMaskSlotEquiv n).symm j <;>
    simp [maskFreshTuple, maskFreshOldTuple, maskFreshNewTuple, freshMaskOldSlot, freshMaskNewSlot]

def maskFreshScalar (y : Bool → ℕ) (b : Bool) (t : Fin 3) : ℕ :=
  if t = 0 then 1 else if t = 1 then y b else y (!b)

theorem maskFreshTuple_eval_old {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ)
    (P : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval (fun j => (maskFreshTuple x y j : ℤ))
      (MvPolynomial.rename (freshMaskOldSlot n) P) =
    MvPolynomial.eval (fun j => (x j : ℤ)) P := by
  rw [MvPolynomial.eval_rename]
  have he : (fun j => (maskFreshTuple x y j : ℤ)) ∘ freshMaskOldSlot n =
      fun j => (x j : ℤ) := by
    funext j
    exact congrArg (fun a : ℕ => (a : ℤ)) (maskFreshTuple_oldSlot x y j)
  rw [he]

theorem maskFreshTuple_eval_multiplier {n : ℕ} (x : Fin n → ℕ) (y : Bool → ℕ)
    (b : Bool) (t : Fin 3) :
    MvPolynomial.eval (fun j => (maskFreshTuple x y j : ℤ))
      (flattenedFreshMaskMultiplier n b t) = (maskFreshScalar y b t : ℤ) := by
  unfold flattenedFreshMaskMultiplier maskFreshScalar
  split_ifs <;> simp [maskFreshTuple_newSlot]

theorem maskFreshTuple_eval_descendantRow {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag)
    (x : Fin n → ℕ) (y : Bool → ℕ) (j : Fin (m + 1)) :
    MvPolynomial.eval (fun k => (maskFreshTuple x y k : ℤ))
      ((F.flattenedMaskStep tag).row (Fintype.equivFin _ d) j) =
      MvPolynomial.eval (fun k => (x k : ℤ)) (F.row d.val.1 j) *
        (d.val.2.elim 1 (fun b => maskFreshScalar y b (tag j)) : ℤ) := by
  rw [flattenedMaskStep_row]
  simp only [Equiv.symm_apply_apply, map_mul, maskFreshTuple_eval_old]
  cases hb : d.val.2 <;> simp [maskFreshTuple_eval_multiplier]

end Hindman168
