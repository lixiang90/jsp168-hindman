import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.Module.Rat

/-! A real bilinear map preserving an actual rational subspace also
preserves its actual real linear span. This is algebraic span induction,
with no assertion that the rational subspace is closed. -/

namespace Hindman168
open Set Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

 theorem rationalBilinear_realSpan_mem (B : E →L[ℝ] (E →L[ℝ] E))
    (V : Submodule ℚ E) (hB : ∀ x ∈ V, ∀ y ∈ V, B x y ∈ V)
    {x y : E} (hx : x ∈ span ℝ (V : Set E)) (hy : y ∈ span ℝ (V : Set E)) :
    B x y ∈ span ℝ (V : Set E) := by
  let S : Submodule ℝ E := span ℝ (V : Set E)
  have hsecond : ∀ v ∈ V, ∀ w ∈ S, B v w ∈ S := by
    intro v hv w hw
    have hle : S ≤ S.comap (B v).toLinearMap := by
      apply span_le.mpr
      intro z hz
      exact subset_span (hB v hv z hz)
    exact hle hw
  have hle : S ≤ S.comap (B.flip y).toLinearMap := by
    apply span_le.mpr
    intro v hv
    exact hsecond v hv y hy
  exact hle hx

end Hindman168
