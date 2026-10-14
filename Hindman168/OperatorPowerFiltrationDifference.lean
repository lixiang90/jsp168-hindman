import Mathlib.Analysis.Normed.Operator.Basic

/-! Genuine operator powers preserve congruence modulo a submodule.
The finite inductive identity is valid without commutation of the two
operators. It will be instantiated with actual native bracket and dexp
defect operators, not with an assumed Picard termination property. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem operator_pow_sub_mem_submodule {P Q : E →L[ℝ] E} (S : Submodule ℝ E)
    (hP : ∀ x : E, x ∈ S → P x ∈ S) (hPQ : ∀ x : E, P x - Q x ∈ S)
    (n : ℕ) (u : E) : (P ^ n) u - (Q ^ n) u ∈ S := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, sub_self, Submodule.zero_mem]
  | succ n ih =>
    have he : (P ^ (n + 1)) u - (Q ^ (n + 1)) u =
        P ((P ^ n) u - (Q ^ n) u) + (P ((Q ^ n) u) - Q ((Q ^ n) u)) := by
      simp only [pow_succ', map_sub]
      abel
    rw [he]
    exact S.add_mem (hP _ ih) (hPQ _)

end Hindman168
