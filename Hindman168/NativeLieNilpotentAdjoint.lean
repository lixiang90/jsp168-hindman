import Hindman168.NativeLieAdjointInfinitesimal
import Mathlib.Algebra.Lie.Nilpotent

/-! The actual native adjoint has a finite formula when the original native
Lie algebra is nilpotent. Nilpotency of its derivative-defined generator is
derived from the original Lie action; it is not assumed separately. These
results do not assert group/Lie lower-central comparison. -/

namespace Hindman168
open Function Set Topology Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_toEnd (v : GroupLieAlgebra I G) :
    (nativeLieAdjointGenerator (I := I) (G := G) v).toLinearMap =
      LieModule.toEnd ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) v := by
  apply LinearMap.ext
  intro w
  exact nativeLieAdjointGenerator_eq_native_bracket v w

 theorem nativeLieAdjointGenerator_uniform_pow_zero
    [LieModule.IsNilpotent (GroupLieAlgebra I G) (GroupLieAlgebra I G)] :
    ∃ k : ℕ, ∀ v : E, nativeLieAdjointGenerator (I := I) (G := G) v ^ k = 0 := by
  obtain ⟨k, hk⟩ := LieModule.exists_forall_pow_toEnd_eq_zero
    ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G)
  refine ⟨k, fun v => ?_⟩
  have hv : (nativeLieAdjointGenerator (I := I) (G := G) v).toLinearMap ^ k = 0 := by
    rw [nativeLieAdjointGenerator_toEnd]
    exact hk v
  have hm : (nativeLieAdjointGenerator (I := I) (G := G) v ^ k).toLinearMap = 0 := by
    calc
      _ = (nativeLieAdjointGenerator (I := I) (G := G) v).toLinearMap ^ k :=
        map_pow ContinuousLinearMap.toLinearMapRingHom _ k
      _ = 0 := hv
  apply ContinuousLinearMap.ext
  intro w
  change (nativeLieAdjointGenerator (I := I) (G := G) v ^ k).toLinearMap w = 0
  rw [hm, LinearMap.zero_apply]

 theorem nativeLieAdjointGenerator_isNilpotent
    [LieModule.IsNilpotent (GroupLieAlgebra I G) (GroupLieAlgebra I G)] (v : E) :
    IsNilpotent (nativeLieAdjointGenerator (I := I) (G := G) v) := by
  obtain ⟨k, hk⟩ := nativeLieAdjointGenerator_uniform_pow_zero (I := I) (G := G)
  exact ⟨k, hk v⟩

 theorem nativeLieAdjointCurve_eq_finite_sum (v : E) {k : ℕ}
    (hk : nativeLieAdjointGenerator (I := I) (G := G) v ^ k = 0) (t : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) v t =
      ∑ j ∈ range k, (j.factorial : ℝ)⁻¹ •
        ((t • nativeLieAdjointGenerator (I := I) (G := G) v) ^ j) := by
  rw [nativeLieAdjointCurve_eq_exp, NormedSpace.exp_eq_tsum ℝ]
  apply tsum_eq_sum
  intro j hj
  have hkj : k ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  have hp : (t • nativeLieAdjointGenerator (I := I) (G := G) v) ^ j = 0 := by
    rw [smul_pow, pow_eq_zero_of_le hkj hk, smul_zero]
  rw [hp, smul_zero]

 theorem nativeLieAdjoint_nilpotent_uniform_finite_formula
    [LieModule.IsNilpotent (GroupLieAlgebra I G) (GroupLieAlgebra I G)] :
    ∃ k : ℕ, ∀ (v : E) (t : ℝ), nativeLieAdjointCurve (I := I) (G := G) v t =
      ∑ j ∈ range k, (j.factorial : ℝ)⁻¹ •
        ((t • nativeLieAdjointGenerator (I := I) (G := G) v) ^ j) := by
  obtain ⟨k, hk⟩ := nativeLieAdjointGenerator_uniform_pow_zero (I := I) (G := G)
  exact ⟨k, fun v t => nativeLieAdjointCurve_eq_finite_sum v (hk v) t⟩

 theorem nativeLieAdjoint_exponential_eq_finite_sum (v : E) {k : ℕ}
    (hk : nativeLieAdjointGenerator (I := I) (G := G) v ^ k = 0) :
    nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) =
      ∑ j ∈ range k, (j.factorial : ℝ)⁻¹ •
        (nativeLieAdjointGenerator (I := I) (G := G) v ^ j) := by
  simpa only [nativeLieAdjointCurve, nativeLieExponential, one_smul]
    using nativeLieAdjointCurve_eq_finite_sum v hk 1

end Hindman168
