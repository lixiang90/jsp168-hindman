import Hindman168.NativeLieExponentialLocalHomeomorph
import Hindman168.NilpotentFiniteExponentialKernel

/-! Every original native exponential period has zero actual adjoint
generator and lies in the center of the original native Lie algebra.
This does not rule out central periods or prove global injectivity. -/

namespace Hindman168
open Function Set Finset Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_eq_zero_of_exponential_eq_one {v : E}
    (hv : nativeLieExponential (I := I) (G := G) v = 1) :
    nativeLieAdjointGenerator (I := I) (G := G) v = 0 := by
  have h := nativeLieAdjoint_exponential_finite_formula_of_group_isNilpotent (I := I) (G := G) v
  rw [hv, nativeLieAdjoint_one] at h
  have he : (∑ j ∈ range (Group.nilpotencyClass G), (j.factorial : ℝ)⁻¹ •
      nativeLieAdjointGenerator (I := I) (G := G) v ^ j) = (1 : E →L[ℝ] E) := h.symm
  exact eq_zero_of_nilpotent_finite_exponential_eq_one
    (nativeLieAdjointGenerator_pow_nilpotencyClass v) he

 theorem nativeLieBracket_eq_zero_of_exponential_eq_one {v : GroupLieAlgebra I G}
    (hv : nativeLieExponential (I := I) (G := G) v = 1) (w : GroupLieAlgebra I G) :
    ⁅v, w⁆ = 0 := by
  rw [← nativeLieAdjointGenerator_eq_native_bracket,
    nativeLieAdjointGenerator_eq_zero_of_exponential_eq_one hv]
  rfl

 theorem nativeLieAdjointCurve_eq_one_of_exponential_eq_one {v : E}
    (hv : nativeLieExponential (I := I) (G := G) v = 1) (t : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) v t = 1 := by
  rw [nativeLieAdjointCurve_eq_exp,
    nativeLieAdjointGenerator_eq_zero_of_exponential_eq_one hv, smul_zero, NormedSpace.exp_zero]

end Hindman168
