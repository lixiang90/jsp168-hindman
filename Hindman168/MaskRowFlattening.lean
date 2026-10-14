import Hindman168.MaskRowFamilyStep
import Hindman168.PolynomialRowFamilyTransport
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Fresh prime slots return to ordinary integer multivariate polynomials

The exact ring equivalence flattens the two fresh variables and old slots
into Fin (2+n). Injective coefficient transport derives the same anchors
and pair minors. Tracked noninvariant descendants retain their old support.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def freshMaskFlatten (n : ℕ) :
    MvPolynomial Bool (MvPolynomial (Fin n) ℤ) ≃+* MvPolynomial (Fin (2 + n)) ℤ :=
  (MvPolynomial.sumRingEquiv ℤ Bool (Fin n)).symm.trans
    (MvPolynomial.renameEquiv ℤ
      ((Equiv.sumCongr finTwoEquiv.symm (Equiv.refl (Fin n))).trans finSumFinEquiv)).toRingEquiv

noncomputable def PolynomialRowFamily.flattenedMaskStep {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) :
    PolynomialRowFamily (MvPolynomial (Fin (2 + n)) ℤ)
      (Fintype.card (MaskDescendant F tag)) m :=
  (F.maskStep tag).mapCoefficients (freshMaskFlatten n).toRingHom (freshMaskFlatten n).injective

noncomputable def maskTrackedRowIndex {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (i : Fin r) (hi : ¬ maskRowInvariant (F.row i) tag) (b : Bool) :
    Fin (Fintype.card (MaskDescendant F tag)) :=
  Fintype.equivFin _ (maskNoninvariantCopy F tag i hi b)

theorem flattenedMaskStep_support_iff {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (x : MaskDescendant F tag) (k : Fin (m + 1)) :
    (F.flattenedMaskStep tag).row (Fintype.equivFin _ x) k ≠ 0 ↔ F.row x.val.1 k ≠ 0 := by
  unfold PolynomialRowFamily.flattenedMaskStep
  rw [PolynomialRowFamily.mapCoefficients_support_iff]
  simpa only [PolynomialRowFamily.maskStep, Equiv.symm_apply_apply] using
    maskDescendant_support_iff F tag x k

theorem flattenedMaskStep_tracked_support {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (i : Fin r)
    (hi : ¬ maskRowInvariant (F.row i) tag) (b : Bool) (k : Fin (m + 1)) :
    (F.flattenedMaskStep tag).row (maskTrackedRowIndex F tag i hi b) k ≠ 0 ↔ F.row i k ≠ 0 :=
  flattenedMaskStep_support_iff F tag (maskNoninvariantCopy F tag i hi b) k

end Hindman168
