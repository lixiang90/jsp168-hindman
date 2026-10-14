import Hindman168.MaskInvariantAbsorptionDensity
import Hindman168.MaskFlattenedCoefficients

/-! The maximum-support normalization anchor, rather than just the
construction anchor, is unchanged by every flattened mask descendant. -/

namespace Hindman168

open scoped BigOperators Classical

variable {n r m : ℕ}

theorem PolynomialRowFamily.flattenedMaskStep_support
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag) :
    (F.flattenedMaskStep tag).support (Fintype.equivFin _ d) = F.support d.val.1 := by
  ext j
  simp only [PolynomialRowFamily.support, Finset.mem_filter, Finset.mem_univ, true_and]
  exact flattenedMaskStep_support_iff F tag d j

theorem PolynomialRowFamily.flattenedMaskStep_normalizationAnchor
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag) :
    (F.flattenedMaskStep tag).normalizationAnchor (Fintype.equivFin _ d) =
      F.normalizationAnchor d.val.1 := by
  apply le_antisymm
  · apply F.le_normalizationAnchor d.val.1
    exact (flattenedMaskStep_support_iff F tag d _).mp
      ((F.flattenedMaskStep tag).normalizationAnchor_ne_zero _)
  · apply (F.flattenedMaskStep tag).le_normalizationAnchor
    exact (flattenedMaskStep_support_iff F tag d _).mpr (F.normalizationAnchor_ne_zero _)

theorem PolynomialRowFamily.flattenedMaskStep_normalizationAnchor_index
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (i : Fin (Fintype.card (MaskDescendant F tag))) :
    (F.flattenedMaskStep tag).normalizationAnchor i =
      F.normalizationAnchor ((Fintype.equivFin (MaskDescendant F tag)).symm i).val.1 := by
  simpa only [Equiv.apply_symm_apply] using
    F.flattenedMaskStep_normalizationAnchor tag ((Fintype.equivFin _).symm i)

end Hindman168
