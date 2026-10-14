import Hindman168.AdditiveRowResidueIndependence

/-! Canonical copies for the root-smoothed first and second moments.
Target copies have a fixed root branch, since the root direction annihilates
that row. Non-target copies can use two independent root variables. -/

namespace Hindman168

open scoped BigOperators Classical

abbrev RootSmoothedAdditiveCopy (b : ℕ) :=
  {r : CopiedReplicaCubeRow (additiveRowAssigned b) × Bool //
    r.1.val.1 = none → r.2 = false}

abbrev RootSmoothedAdditiveColumn (b c : ℕ) := AdditiveCopiedColumn b c ⊕ Bool

noncomputable def rootSmoothedCopy {b : ℕ}
    (r : CopiedReplicaCubeRow (additiveRowAssigned b)) (bit : Bool)
    (h : r.val.1 = none → bit = false) : RootSmoothedAdditiveCopy b := ⟨(r, bit), h⟩

noncomputable def rootSmoothedTargetCopy {b : ℕ} (η : Fin b → Bool) :
    RootSmoothedAdditiveCopy b :=
  rootSmoothedCopy (replicaRootCopy (additiveRowAssigned b) η) false (fun _ => rfl)

theorem rootSmoothedTargetCopy_injective (b : ℕ) :
    Function.Injective (@rootSmoothedTargetCopy b) := by
  intro η θ he
  apply replicaRootCopy_injective (additiveRowAssigned b)
  exact congrArg (fun r : RootSmoothedAdditiveCopy b => r.val.1) he

theorem rootSmoothedAdditiveColumn_card (b c : ℕ) :
    Fintype.card (RootSmoothedAdditiveColumn b c) = c + 2 * b + 2 := by
  simp only [RootSmoothedAdditiveColumn, AdditiveCopiedColumn, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

theorem rootSmoothedAdditiveCopy_card_le (b : ℕ) :
    Fintype.card (RootSmoothedAdditiveCopy b) ≤
      2 * Fintype.card (CopiedReplicaCubeRow (additiveRowAssigned b)) := by
  have h := Fintype.card_subtype_le
    (fun r : CopiedReplicaCubeRow (additiveRowAssigned b) × Bool =>
      r.1.val.1 = none → r.2 = false)
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

namespace AdditiveRowData

variable {b c : ℕ}

noncomputable def rootSmoothedCoefficient (D : AdditiveRowData b c) (v₀ : Fin c → ℤ)
    (r : RootSmoothedAdditiveCopy b) (col : RootSmoothedAdditiveColumn b c) : ℤ :=
  match col with
  | .inl j => D.copiedCoefficient r.val.1 j
  | .inr bit => if bit = r.val.2 then D.form r.val.1.val.1 v₀ else 0

noncomputable def rootSmoothedFinCoefficient (D : AdditiveRowData b c) (v₀ : Fin c → ℤ)
    (r : RootSmoothedAdditiveCopy b)
    (j : Fin (Fintype.card (RootSmoothedAdditiveColumn b c))) : ℤ :=
  D.rootSmoothedCoefficient v₀ r ((Fintype.equivFin (RootSmoothedAdditiveColumn b c)).symm j)

theorem rootSmoothedCoefficient_eval (D : AdditiveRowData b c) (v₀ : Fin c → ℤ)
    (r : RootSmoothedAdditiveCopy b) (z : Fin c → ℤ) (v : Fin b → Bool → ℤ)
    (u₀ : Bool → ℤ) :
    (∑ j, D.rootSmoothedCoefficient v₀ r j *
      Sum.elim (Sum.elim z (fun kb => v kb.1 kb.2)) u₀ j) =
      D.translatedForm r.val.1.val.1 r.val.1.val.2 z v +
        D.form r.val.1.val.1 v₀ * u₀ r.val.2 := by
  rw [Fintype.sum_sum_type]
  simp only [rootSmoothedCoefficient, Sum.elim_inl, Sum.elim_inr]
  rw [D.copiedCoefficient_eval]
  congr 1
  cases r.val.2 <;> simp only [Fintype.sum_bool, Bool.true_eq_false,
    Bool.false_eq_true, ite_false, ite_true, zero_mul, zero_add, add_zero]

theorem rootSmoothedCoefficient_eval_translate (D : AdditiveRowData b c)
    (v₀ : Fin c → ℤ) (r : RootSmoothedAdditiveCopy b)
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) (u₀ : Bool → ℤ) :
    (∑ j, D.rootSmoothedCoefficient v₀ r j *
      Sum.elim (Sum.elim z (fun kb => v kb.1 kb.2)) u₀ j) =
      D.translatedForm r.val.1.val.1 r.val.1.val.2
        (fun j => z j + u₀ r.val.2 * v₀ j) v := by
  rw [D.rootSmoothedCoefficient_eval]
  simp only [translatedForm, D.form_add, D.form_mul]
  ring

theorem rootSmoothedFinCoefficient_eval (D : AdditiveRowData b c) (v₀ : Fin c → ℤ)
    (r : RootSmoothedAdditiveCopy b) (z : RootSmoothedAdditiveColumn b c → ℤ) :
    (∑ j, D.rootSmoothedFinCoefficient v₀ r j *
      z ((Fintype.equivFin (RootSmoothedAdditiveColumn b c)).symm j)) =
      ∑ col, D.rootSmoothedCoefficient v₀ r col * z col :=
  Fintype.sum_equiv (Fintype.equivFin (RootSmoothedAdditiveColumn b c)).symm _ _ (fun _ => rfl)

end AdditiveRowData
end Hindman168
