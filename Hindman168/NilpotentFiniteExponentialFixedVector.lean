import Hindman168.NilpotentFiniteExponentialKernel
import Mathlib.Analysis.Normed.Operator.Banach

/-! Fixed vectors of the actual finite exponential of a nilpotent
continuous linear map are exactly its kernel. The constant-one
polynomial factor is a genuine invertible operator, including cutoff zero. -/

namespace Hindman168
open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem nilpotent_finite_exponential_fixed_vector {B : E →L[ℝ] E} {k : ℕ}
    (hB : B ^ k = 0) {w : E}
    (hw : (∑ j ∈ range k, (j.factorial : ℝ)⁻¹ • B ^ j) w = w) : B w = 0 := by
  let Q : E →L[ℝ] E := ∑ j ∈ range k, ((j + 1).factorial : ℝ)⁻¹ • B ^ j
  have hQ : IsUnit Q := by
    apply nilpotent_polynomial_isUnit hB
    simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one]
  have hc : Commute B Q := by
    apply Commute.sum_right
    intro j _
    exact ((Commute.refl B).pow_right j).smul_right _
  have hf := congrArg (fun T : E →L[ℝ] E => T w)
    (nilpotent_finite_exponential_factor (𝕜 := ℝ) hB)
  change (B * Q) w + w = (∑ j ∈ range k, (j.factorial : ℝ)⁻¹ • B ^ j) w at hf
  rw [hw, hc.eq] at hf
  have hz : Q (B w) = 0 := add_right_cancel (hf.trans (zero_add w).symm)
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hQ).1 (hz.trans Q.map_zero.symm)

end Hindman168
