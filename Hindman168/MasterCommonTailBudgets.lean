import Hindman168.MasterTailGapBudgets

/-!
# The paper's actual common tail budget

V_T = 2 + M + product_{j in T} X_j^2 covers only the shared tail.
It lies below every auxiliary value after that tail, including gaps
strictly before the pivot. No full-pivot divisor cap is needed.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def masterCommonTailBudget (F : MasterParameterFamily)
    (w : ℕ) (T : Finset ℕ) : ℕ :=
  2 + (F.modulus w : ℕ) + ∏ j ∈ T, F.cutoff w j ^ 2

theorem masterCommonTailBudget_ge_two (F : MasterParameterFamily) (w : ℕ) (T : Finset ℕ) :
    2 ≤ masterCommonTailBudget F w T := by unfold masterCommonTailBudget; omega

theorem masterCommonTailBudget_modulus (F : MasterParameterFamily) (w : ℕ) (T : Finset ℕ) :
    (F.modulus w : ℕ) ≤ masterCommonTailBudget F w T := by unfold masterCommonTailBudget; omega

theorem masterCommonTailBudget_tail_product (F : MasterParameterFamily) (w : ℕ) (T : Finset ℕ) :
    (∏ j ∈ T, F.cutoff w j ^ 2) ≤ masterCommonTailBudget F w T := by
  unfold masterCommonTailBudget
  omega

theorem MasterParameterConditions.common_tail_divisor_budget {n N m : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : Chain m) (w : ℕ) (i : Fin m)
    (T : Finset ℕ) (htail : C.tail i ⊆ T) :
    tailBound (C.tailCutoffs (F.cutoff w) i) ≤ masterCommonTailBudget F w T := by
  rw [chain_tailBound_eq]
  have hp : (∏ j ∈ C.tail i, F.cutoff w j ^ 2) ≤ ∏ j ∈ T, F.cutoff w j ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le' htail
      (fun j _ _ => one_le_pow₀ (hF.cutoff_positive w j))
  exact hp.trans (masterCommonTailBudget_tail_product F w T)

theorem MasterParameterConditions.common_tail_budget_le_auxiliary {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w l : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range l) :
    masterCommonTailBudget F w T ≤ F.auxiliary w l := by
  have hp : (∏ j ∈ T, F.cutoff w j ^ 2) ≤ ∏ j ∈ Finset.range l, F.cutoff w j ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le' hT
      (fun j _ _ => one_le_pow₀ (hF.cutoff_positive w j))
  unfold masterCommonTailBudget MasterParameterFamily.auxiliary
  omega

theorem masterCommonTailBudget_chain_tail (F : MasterParameterFamily)
    {m : ℕ} (C : Chain m) (w : ℕ) (i : Fin m) :
    masterCommonTailBudget F w (C.tail i) =
      2 + (F.modulus w : ℕ) + tailBound (C.tailCutoffs (F.cutoff w) i) := by
  rw [chain_tailBound_eq]
  rfl

theorem MasterParameterConditions.common_tail_budget_at_pivot {n N m : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : Chain m) (w : ℕ) (i : Fin m) :
    masterCommonTailBudget F w (C.tail i) ≤ F.auxiliary w (C.pivot i) := by
  apply hF.common_tail_budget_le_auxiliary
  intro j hj
  exact Finset.mem_range.mpr (C.tails_before_pivots i i j hj)

end Hindman168
