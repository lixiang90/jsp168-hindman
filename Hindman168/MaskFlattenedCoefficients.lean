import Hindman168.MaskRowFlattening
import Mathlib.Algebra.MvPolynomial.Variables

/-! Exact old/fresh slot identities for the already constructed flattening. -/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def freshMaskSlotEquiv (n : ℕ) : Bool ⊕ Fin n ≃ Fin (2 + n) :=
  (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl (Fin n))).trans finSumFinEquiv

noncomputable def freshMaskOldSlot (n : ℕ) (k : Fin n) : Fin (2 + n) :=
  freshMaskSlotEquiv n (Sum.inr k)

noncomputable def freshMaskNewSlot (n : ℕ) (b : Bool) : Fin (2 + n) :=
  freshMaskSlotEquiv n (Sum.inl b)

theorem freshMaskOldSlot_injective (n : ℕ) : Function.Injective (freshMaskOldSlot n) := by
  intro a b h
  exact Sum.inr.inj ((freshMaskSlotEquiv n).injective h)

theorem freshMaskNewSlot_injective (n : ℕ) : Function.Injective (freshMaskNewSlot n) := by
  intro a b h
  exact Sum.inl.inj ((freshMaskSlotEquiv n).injective h)

theorem freshMaskNewSlot_ne_old (n : ℕ) (b : Bool) (k : Fin n) :
    freshMaskNewSlot n b ≠ freshMaskOldSlot n k := by
  intro h
  have he := (freshMaskSlotEquiv n).injective h
  cases he

theorem freshMaskFlatten_C (n : ℕ) (P : MvPolynomial (Fin n) ℤ) :
    freshMaskFlatten n (MvPolynomial.C P) = MvPolynomial.rename (freshMaskOldSlot n) P := by
  have hC : (MvPolynomial.sumRingEquiv ℤ Bool (Fin n)).symm (MvPolynomial.C P) =
      MvPolynomial.rename Sum.inr P := by
    apply MvPolynomial.induction_on P
    · intro a
      simp
    · intro P Q hP hQ
      simp [hP, hQ]
    · intro P i hP
      simp [hP]
  change MvPolynomial.rename (freshMaskSlotEquiv n)
    ((MvPolynomial.sumRingEquiv ℤ Bool (Fin n)).symm (MvPolynomial.C P)) = _
  rw [hC, MvPolynomial.rename_rename]
  rfl

theorem freshMaskFlatten_X (n : ℕ) (b : Bool) :
    freshMaskFlatten n (MvPolynomial.X b) = MvPolynomial.X (freshMaskNewSlot n b) := by
  change MvPolynomial.rename (freshMaskSlotEquiv n)
    ((MvPolynomial.sumRingEquiv ℤ Bool (Fin n)).symm (MvPolynomial.X b)) = _
  rw [MvPolynomial.sumRingEquiv_symm_X, MvPolynomial.rename_X]
  rfl

noncomputable def flattenedFreshMaskMultiplier (n : ℕ) (b : Bool) (t : Fin 3) :
    MvPolynomial (Fin (2 + n)) ℤ :=
  if t = 0 then 1 else if t = 1 then MvPolynomial.X (freshMaskNewSlot n b)
  else MvPolynomial.X (freshMaskNewSlot n (!b))

theorem freshMaskFlatten_multiplier (n : ℕ) (b : Bool) (t : Fin 3) :
    freshMaskFlatten n (freshMaskMultiplier b t) = flattenedFreshMaskMultiplier n b t := by
  unfold freshMaskMultiplier flattenedFreshMaskMultiplier
  split_ifs <;> simp only [map_one, freshMaskFlatten_X]

theorem freshMaskFlatten_row {n c : ℕ} (A : Fin c → MvPolynomial (Fin n) ℤ)
    (tag : Fin c → Fin 3) (b : Option Bool) (k : Fin c) :
    freshMaskFlatten n (maskBranchRow A tag b k) =
      MvPolynomial.rename (freshMaskOldSlot n) (A k) *
        b.elim 1 (fun bb => flattenedFreshMaskMultiplier n bb (tag k)) := by
  cases b <;> simp [maskBranchRow, freshMaskFlatten_C, freshMaskFlatten_multiplier]

theorem flattenedMaskStep_row {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3)
    (i : Fin (Fintype.card (MaskDescendant F tag))) (k : Fin (m + 1)) :
    (F.flattenedMaskStep tag).row i k =
      MvPolynomial.rename (freshMaskOldSlot n)
        (F.row ((Fintype.equivFin (MaskDescendant F tag)).symm i).val.1 k) *
        ((Fintype.equivFin (MaskDescendant F tag)).symm i).val.2.elim 1
          (fun bb => flattenedFreshMaskMultiplier n bb (tag k)) :=
  freshMaskFlatten_row _ _ _ _

end Hindman168
