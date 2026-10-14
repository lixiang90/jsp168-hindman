import Hindman168.MaskMonomialRowStructure
import Hindman168.MaskGeneratedOriginalTemplates

/-! The actual full mask iteration has monomial/column-slot certificates. -/

namespace Hindman168

open scoped BigOperators Classical

theorem PolynomialMonomialRow.monomial_of_ne_zero {n c : ℕ}
    {A : Fin c → MvPolynomial (Fin n) ℤ} (hA : PolynomialMonomialRow A) (k : Fin c)
    (hk : A k ≠ 0) : CoefficientOneMonomial (A k) :=
  (hA.entries k).resolve_left hk

theorem initialTargetedMaskRowStage_monomial {m : ℕ}
    (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    (initialTargetedMaskRowStage S hS).rows.MonomialStructure :=
  initialMaskRowFamily_monomial m

theorem TargetedMaskRowStage.step_monomial {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hF : F.rows.MonomialStructure)
    (hS : 2 ≤ S.card) (U : Finset (Fin (m + 1))) :
    (F.step hS U).rows.MonomialStructure := by
  exact PolynomialRowFamily.MonomialStructure.flattened_step F.rows hF
    (chosenMaskColumnPlan S U hS).tag (chosenMaskColumnPlan S U hS).tag_unique_nonzero

theorem TargetedMaskRowStage.iterate_monomial {m : ℕ} {S : Finset (Fin (m + 1))}
    (F : TargetedMaskRowStage S) (hF : F.rows.MonomialStructure)
    (hS : 2 ≤ S.card) (masks : List (Finset (Fin (m + 1)))) :
    (F.iterate hS masks).rows.MonomialStructure := by
  induction masks generalizing F with
  | nil => simpa only [iterate, List.foldl_nil] using hF
  | cons U rest ih =>
    change ((F.step hS U).iterate hS rest).rows.MonomialStructure
    exact ih _ (F.step_monomial hF hS U)

theorem fullMaskRowStage_monomial {m : ℕ}
    (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    (fullMaskRowStage S hS).rows.MonomialStructure :=
  (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate_monomial
    (initialTargetedMaskRowStage_monomial _ _) hS _

theorem maskGeneratedRowData_monomial {m N : ℕ}
    (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) (gap : ℕ → Fin N) :
    (maskGeneratedRowData S hS gap).rows.MonomialStructure :=
  fullMaskRowStage_monomial S hS

theorem maskGeneratedRowDataFamily_monomial (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (t : Fin (Fintype.card (LargeColumnSubset m))) :
    (maskGeneratedRowDataFamily m gap t).rows.MonomialStructure :=
  maskGeneratedRowData_monomial _ _ gap

end Hindman168
