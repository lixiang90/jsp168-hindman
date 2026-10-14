import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace Hindman168
open scoped BigOperators Classical

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  (V : ι → Submodule ℝ E) [∀ i, (V i).HasOrthogonalProjection]

omit [Fintype ι] in
/-- The correlation of a vector with one of its genuine orthogonal
projections is exactly the squared norm of that projection. -/
theorem finiteProjection_inner_eq_energy (z : E) (i : ι) :
    inner ℝ z ((V i).starProjection z) = ‖(V i).starProjection z‖ ^ 2 := by
  have h := (V i).starProjection_inner_eq_zero z ((V i).starProjection z)
    ((V i).starProjection_apply_mem z)
  rw [inner_sub_left, sub_eq_zero, real_inner_self_eq_norm_sq] at h
  exact h

/-- Bessel energy for a finite family of projections of one vector.
Only the projected vectors need to be pairwise orthogonal; the whole
subspaces need not be mutually orthogonal. -/
theorem finiteProjection_bessel_energy (z : E)
    (ho : ∀ i j : ι, i ≠ j →
      inner ℝ ((V i).starProjection z) ((V j).starProjection z) = 0) :
    ∑ i, ‖(V i).starProjection z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  let y := ∑ i, (V i).starProjection z
  have hy : ‖y‖ ^ 2 = ∑ i, ‖(V i).starProjection z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (∑ i, (V i).starProjection z) (∑ i, (V i).starProjection z) = _
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    rw [Fintype.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq _
    · intro j hj
      exact ho i j (Ne.symm hj)
  have hi : inner ℝ z y = ∑ i, ‖(V i).starProjection z‖ ^ 2 := by
    change inner ℝ z (∑ i, (V i).starProjection z) = _
    rw [inner_sum]
    exact Finset.sum_congr rfl (fun i _ => finiteProjection_inner_eq_energy V z i)
  have hn : 0 ≤ inner ℝ (z - y) (z - y) := real_inner_self_nonneg
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hn
  have hiy : inner ℝ y z = ∑ i, ‖(V i).starProjection z‖ ^ 2 :=
    (real_inner_comm z y).trans hi
  rw [hi, hiy, hy] at hn
  linarith

end Hindman168
