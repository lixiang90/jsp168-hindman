import Hindman168.MasterTranslationScales
import Hindman168.MasterDivisorSampling

/-!
# Actual tail budgets and the coarse pivot-budget obstruction

Prediction gaps lie after the common tail but before the root pivot.
Their admissible divisor cap is the actual tail product. Bounding that
product instead by the full auxiliary value at the pivot is too coarse:
at a valid earlier gap, requiring pivot auxiliary <= V <= gap auxiliary
is inconsistent. This is an application-interface issue, not a failure
of the paper's tail-based budget or of the conditional kernel proofs.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem MasterParameterConditions.chain_tail_budget_at_gap {n N m : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : Chain m) (w : ℕ) (i : Fin m) (l : ℕ)
    (htail : C.tail i ⊆ Finset.range l) :
    tailBound (C.tailCutoffs (F.cutoff w) i) ≤ F.auxiliary w l := by
  rw [chain_tailBound_eq]
  exact hF.earlier_tail_product_bound w l (C.tail i) htail

theorem MasterParameterConditions.auxiliary_lt_after_valid_index {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w l i : ℕ) (hli : l < i)
    (hX : 2 ≤ F.cutoff w l) : F.auxiliary w l < F.auxiliary w i := by
  have hp : 0 < ∏ j ∈ Finset.range l, F.cutoff w j ^ 2 :=
    Finset.prod_pos (fun j _ => Nat.pow_pos (hF.cutoff_positive w j))
  have hs : F.auxiliary w l < F.auxiliary w (l + 1) := by
    unfold MasterParameterFamily.auxiliary
    rw [Finset.prod_range_succ]
    have hsq : 4 ≤ F.cutoff w l ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_left (∏ j ∈ Finset.range l, F.cutoff w j ^ 2) hsq
    nlinarith only [hp, hmul]
  exact hs.trans_le (hF.auxiliary_monotone w (by omega : l + 1 ≤ i))

theorem MasterParameterConditions.coarse_pivot_gap_budgets_inconsistent {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w l i V : ℕ) (hli : l < i)
    (hX : 2 ≤ F.cutoff w l) :
    ¬ (F.auxiliary w i ≤ V ∧ V ≤ F.auxiliary w l) := by
  intro h
  exact (Nat.not_le_of_gt (hF.auxiliary_lt_after_valid_index w l i hli hX))
    (h.1.trans h.2)


end Hindman168
