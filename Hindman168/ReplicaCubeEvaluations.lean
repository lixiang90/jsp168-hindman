import Hindman168.ReplicaCubeRows

/-!
# Evaluation of the actual prediction replica cube rows

The coefficient array is exactly the paper's integer cube form. The explicit
binary direction fixes its selected vertex, moves every other vertex and the
root, and also moves every row in another replica.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def replicaCubeEval {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → R) (r : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → R) : R :=
  ∑ col, replicaCubeCoefficient M r col * z col

theorem replicaCubeEval_root {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → R) (z : ReplicaCubeColumn b d → R) :
    replicaCubeEval M none z = z none := by
  simp [replicaCubeEval, Fintype.sum_option, replicaCubeCoefficient]

theorem replicaCubeEval_vertex {R : Type*} [CommRing R] {b d : ℕ}
    (M : Fin b → R) (q : Fin b) (S : CubeVertex d) (z : ReplicaCubeColumn b d → R) :
    replicaCubeEval M (some (q, S)) z =
      z none + M q * ∑ j ∈ S.val, (z (some (q, j, true)) - z (some (q, j, false))) := by
  simp only [replicaCubeEval, Fintype.sum_option, Fintype.sum_prod_type,
    Fintype.sum_bool, replicaCubeCoefficient, one_mul, Bool.false_eq_true, ite_true, ite_false]
  congr 1
  have hterm (q' : Fin b) (j : Fin d) :
      (if q' = q ∧ j ∈ S.val then M q else 0) * z (some (q', j, true)) +
        (if q' = q ∧ j ∈ S.val then -(M q) else 0) * z (some (q', j, false)) =
      if q' = q then (if j ∈ S.val then M q *
        (z (some (q, j, true)) - z (some (q, j, false))) else 0) else 0 := by
    split_ifs <;> simp_all [sub_eq_add_neg, mul_add]
  simp_rw [hterm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Fintype.sum_ite_mem, Finset.mul_sum]

theorem replicaCubeFinCoefficient_eval {b d : ℕ} (M : Fin b → ℤ)
    (r : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → ℤ) :
    (∑ j, replicaCubeFinCoefficient M r j *
      z ((Fintype.equivFin (ReplicaCubeColumn b d)).symm j)) = replicaCubeEval M r z := by
  exact Fintype.sum_equiv (Fintype.equivFin (ReplicaCubeColumn b d)).symm _ _ (fun _ => rfl)

noncomputable def replicaCubeDirection {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) (col : ReplicaCubeColumn b d) : ℤ :=
  match col with
  | none => cubeRootDirection S.val * M q
  | some (q', j, bit) => if q' = q ∧ bit = true then cubeShiftDirection j else 0

theorem replicaCubeDirection_root_response {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) :
    replicaCubeEval M none (replicaCubeDirection M q S) = cubeRootDirection S.val * M q := by
  rw [replicaCubeEval_root]
  rfl

theorem replicaCubeDirection_same_response {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S T : CubeVertex d) :
    replicaCubeEval M (some (q, T)) (replicaCubeDirection M q S) =
      M q * cubeDirectionResponse S.val T.val := by
  rw [replicaCubeEval_vertex]
  simp only [replicaCubeDirection, and_self, ite_true, Bool.false_eq_true,
    and_false, ite_false, sub_zero, cubeDirectionResponse]
  ring

theorem replicaCubeDirection_other_response {b d : ℕ} (M : Fin b → ℤ)
    (q q' : Fin b) (S T : CubeVertex d) (hqq' : q' ≠ q) :
    replicaCubeEval M (some (q', T)) (replicaCubeDirection M q S) =
      cubeRootDirection S.val * M q := by
  rw [replicaCubeEval_vertex]
  simp only [replicaCubeDirection, hqq', false_and, ite_false, sub_self,
    Finset.sum_const_zero, mul_zero, add_zero]

theorem replicaCubeDirection_selected_fixed {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) :
    replicaCubeEval M (some (q, S)) (replicaCubeDirection M q S) = 0 := by
  rw [replicaCubeDirection_same_response, cubeDirectionResponse_self, mul_zero]

theorem replicaCubeDirection_root_moved {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) (hM : M q ≠ 0) :
    replicaCubeEval M none (replicaCubeDirection M q S) ≠ 0 := by
  rw [replicaCubeDirection_root_response]
  exact mul_ne_zero (cubeRootDirection_ne_zero S.property) hM

theorem replicaCubeDirection_other_moved {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) (hM : M q ≠ 0)
    (r : ReplicaCubeRow b d) (hr : r ≠ some (q, S)) :
    replicaCubeEval M r (replicaCubeDirection M q S) ≠ 0 := by
  cases r with
  | none => exact replicaCubeDirection_root_moved M q S hM
  | some r =>
    rcases r with ⟨q', T⟩
    by_cases hq : q' = q
    · subst q'
      rw [replicaCubeDirection_same_response]
      exact mul_ne_zero hM (cubeDirectionResponse_ne_zero (fun h =>
        hr (congrArg (fun T => some (q, T)) (Subtype.ext h.symm))))
    · rw [replicaCubeDirection_other_response M q q' S T hq]
      exact mul_ne_zero (cubeRootDirection_ne_zero S.property) hM

theorem replicaCubeEval_translate {b d : ℕ} (M : Fin b → ℤ)
    (r : ReplicaCubeRow b d) (z v : ReplicaCubeColumn b d → ℤ) (t : ℤ) :
    replicaCubeEval M r (fun col => z col + t * v col) =
      replicaCubeEval M r z + t * replicaCubeEval M r v := by
  simp only [replicaCubeEval, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro col _
  ring

theorem replicaCubeDirection_selected_translate {b d : ℕ} (M : Fin b → ℤ)
    (q : Fin b) (S : CubeVertex d) (z : ReplicaCubeColumn b d → ℤ) (t : ℤ) :
    replicaCubeEval M (some (q, S))
      (fun col => z col + t * replicaCubeDirection M q S col) =
      replicaCubeEval M (some (q, S)) z := by
  rw [replicaCubeEval_translate, replicaCubeDirection_selected_fixed, mul_zero, add_zero]

end Hindman168
