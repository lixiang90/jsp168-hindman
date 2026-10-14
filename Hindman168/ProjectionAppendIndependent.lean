import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic

namespace Hindman168
open scoped BigOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem projection_append_linear_independent {m n : ℕ}
    (π : E →ₗ[ℝ] F) (u : Fin m → E) (c : Fin n → E)
    (hu : LinearIndependent ℝ (fun i => π (u i))) (hc : LinearIndependent ℝ c)
    (hk : ∀ i, π (c i) = 0) : LinearIndependent ℝ (Fin.append u c) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  rw [Fin.sum_univ_add] at ha
  simp only [Fin.append_left, Fin.append_right] at ha
  have hp : ∑ i, a (Fin.castAdd n i) • π (u i) = 0 := by
    have h := congrArg π ha
    simpa only [map_add, map_sum, map_smul, hk, smul_zero, Finset.sum_const_zero,
      add_zero, map_zero] using h
  have hL := Fintype.linearIndependent_iff.mp hu (fun i => a (Fin.castAdd n i)) hp
  have hRsum : ∑ i, a (Fin.natAdd m i) • c i = 0 := by
    simpa only [hL, zero_smul, Finset.sum_const_zero, zero_add] using ha
  have hR := Fintype.linearIndependent_iff.mp hc (fun i => a (Fin.natAdd m i)) hRsum
  intro i
  cases i using Fin.addCases with
  | left i => exact hL i
  | right i => exact hR i

end Hindman168
