import Hindman168.CopiedReplicaCubeRows

/-!
# Canonicalization and actual evaluation of duplicated cube rows

Setting zero-response branches to false leaves the translated form unchanged.
The remaining independent branches give genuinely different canonical copies.
The integer array evaluates exactly to the original row plus its selected
duplicated direction variables, with all original integer coefficients.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def canonicalReplicaCubeCopy {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (r : ReplicaCubeRow b d)
    (η : Fin h → Bool) : CopiedReplicaCubeRow dir :=
  ⟨(r, fun i => if r = some (dir i) then false else η i), by
    intro i hi
    simp only [if_pos hi]⟩

theorem canonicalReplicaCubeCopy_base {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (r : ReplicaCubeRow b d) (η : Fin h → Bool) :
    (canonicalReplicaCubeCopy dir r η).val.1 = r := rfl

theorem canonicalReplicaCubeCopy_id {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir) :
    canonicalReplicaCubeCopy dir r.val.1 r.val.2 = r := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    by_cases hi : r.val.1 = some (dir i)
    · simp only [canonicalReplicaCubeCopy, if_pos hi, r.property i hi]
    · simp only [canonicalReplicaCubeCopy, if_neg hi]

theorem canonicalReplicaCubeCopy_eq_iff {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (r : ReplicaCubeRow b d) (η θ : Fin h → Bool) :
    canonicalReplicaCubeCopy dir r η = canonicalReplicaCubeCopy dir r θ ↔
      ∀ i, r ≠ some (dir i) → η i = θ i := by
  constructor
  · intro he i hi
    have h := congrArg (fun v : CopiedReplicaCubeRow dir => v.val.2 i) he
    simpa only [canonicalReplicaCubeCopy, if_neg hi] using h
  · intro he
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      by_cases hi : r = some (dir i)
      · simp only [canonicalReplicaCubeCopy, if_pos hi]
      · simp only [canonicalReplicaCubeCopy, if_neg hi, he i hi]

noncomputable def copiedReplicaCubeForm {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : ReplicaCubeRow b d) (η : Fin h → Bool)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) : ℤ :=
  replicaCubeEval M r z + ∑ i,
    replicaCubeResponseConstant (dir i).1 (dir i).2 r * M (dir i).1 * v i (η i)

theorem copiedReplicaCubeForm_canonical {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : ReplicaCubeRow b d) (η : Fin h → Bool)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) :
    copiedReplicaCubeForm M dir (canonicalReplicaCubeCopy dir r η).val.1
      (canonicalReplicaCubeCopy dir r η).val.2 z v = copiedReplicaCubeForm M dir r η z v := by
  unfold copiedReplicaCubeForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r = some (dir i)
  · have hz := (replicaCubeResponseConstant_zero_iff (dir i).1 (dir i).2 r).mpr hi
    simp only [canonicalReplicaCubeCopy, hz, zero_mul]
  · simp only [canonicalReplicaCubeCopy, if_neg hi]

theorem copiedReplicaCubeCoefficient_eval {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) :
    (∑ col, copiedReplicaCubeCoefficient M dir r col *
      Sum.elim z (fun ib => v ib.1 ib.2) col) =
      copiedReplicaCubeForm M dir r.val.1 r.val.2 z v := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, copiedReplicaCubeCoefficient,
    Sum.elim_inl, Sum.elim_inr, copiedReplicaCubeForm, replicaCubeEval]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases r.val.2 i <;> simp only [Fintype.sum_bool, Bool.true_eq_false,
    Bool.false_eq_true, ite_false, ite_true, zero_mul, zero_add, add_zero, Int.cast_id]

theorem copiedReplicaCubeFinCoefficient_eval {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir)
    (z : CopiedReplicaCubeColumn b d h → ℤ) :
    (∑ j, copiedReplicaCubeFinCoefficient M dir r j *
      z ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j)) =
      ∑ col, copiedReplicaCubeCoefficient M dir r col * z col :=
  Fintype.sum_equiv (Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm _ _ (fun _ => rfl)

theorem replicaCubeEval_sum {b d : ℕ} {ι : Type*} [Fintype ι] (M : Fin b → ℤ)
    (r : ReplicaCubeRow b d) (z : ι → ReplicaCubeColumn b d → ℤ) :
    replicaCubeEval M r (fun col => ∑ i, z i col) = ∑ i, replicaCubeEval M r (z i) := by
  simp only [replicaCubeEval, Finset.mul_sum]
  exact Finset.sum_comm

theorem replicaCubeEval_add {b d : ℕ} (M : Fin b → ℤ) (r : ReplicaCubeRow b d)
    (z v : ReplicaCubeColumn b d → ℤ) :
    replicaCubeEval M r (fun col => z col + v col) = replicaCubeEval M r z + replicaCubeEval M r v := by
  simp only [replicaCubeEval, mul_add, Finset.sum_add_distrib]

theorem replicaCubeEval_mul {b d : ℕ} (M : Fin b → ℤ) (r : ReplicaCubeRow b d)
    (v : ReplicaCubeColumn b d → ℤ) (t : ℤ) :
    replicaCubeEval M r (fun col => t * v col) = t * replicaCubeEval M r v := by
  simp only [replicaCubeEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  ring

theorem copiedReplicaCubeForm_translate {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : ReplicaCubeRow b d) (η : Fin h → Bool)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) :
    replicaCubeEval M r (fun col => z col +
      ∑ i, v i (η i) * replicaCubeDirection M (dir i).1 (dir i).2 col) =
      copiedReplicaCubeForm M dir r η z v := by
  rw [replicaCubeEval_add, replicaCubeEval_sum]
  simp only [replicaCubeEval_mul, replicaCubeDirection_response_factor]
  unfold copiedReplicaCubeForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end Hindman168
