import Hindman168.AdditiveRowTranslations

/-! Actual copied coefficient arrays for the general integer-row recurrence. -/

namespace Hindman168

open scoped BigOperators Classical

abbrev AdditiveCopiedColumn (b c : ℕ) := Fin c ⊕ (Fin b × Bool)

theorem additiveCopiedColumn_card (b c : ℕ) :
    Fintype.card (AdditiveCopiedColumn b c) = c + 2 * b := by
  simp only [AdditiveCopiedColumn, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  omega

namespace AdditiveRowData

variable {b c : ℕ}

theorem form_single (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1) (j : Fin c) :
    D.form i (Pi.single j 1) = D.coefficient i j := by
  simp [form, Pi.single_apply]

noncomputable def copiedCoefficient (D : AdditiveRowData b c)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b)) (col : AdditiveCopiedColumn b c) : ℤ :=
  match col with
  | .inl j => D.coefficient r.val.1 j
  | .inr (k, bit) => if bit = r.val.2 k then D.response r.val.1 k else 0

theorem copiedCoefficient_base (D : AdditiveRowData b c)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b)) (j : Fin c) :
    D.copiedCoefficient r (.inl j) = D.coefficient r.val.1 j := rfl

theorem copiedCoefficient_eval (D : AdditiveRowData b c)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b))
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) :
    (∑ col, D.copiedCoefficient r col * Sum.elim z (fun kb => v kb.1 kb.2) col) =
      D.translatedForm r.val.1 r.val.2 z v := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, copiedCoefficient,
    Sum.elim_inl, Sum.elim_inr, translatedForm, form]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  cases r.val.2 k <;> simp only [Fintype.sum_bool, Bool.true_eq_false,
    Bool.false_eq_true, ite_false, ite_true, zero_mul, zero_add, add_zero]

noncomputable def copiedFinCoefficient (D : AdditiveRowData b c)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b))
    (j : Fin (Fintype.card (AdditiveCopiedColumn b c))) : ℤ :=
  D.copiedCoefficient r ((Fintype.equivFin (AdditiveCopiedColumn b c)).symm j)

theorem copiedFinCoefficient_eval (D : AdditiveRowData b c)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b)) (z : AdditiveCopiedColumn b c → ℤ) :
    (∑ j, D.copiedFinCoefficient r j *
      z ((Fintype.equivFin (AdditiveCopiedColumn b c)).symm j)) =
      ∑ col, D.copiedCoefficient r col * z col :=
  Fintype.sum_equiv (Fintype.equivFin (AdditiveCopiedColumn b c)).symm _ _ (fun _ => rfl)

end AdditiveRowData
end Hindman168
