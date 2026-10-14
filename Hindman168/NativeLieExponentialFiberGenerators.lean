import Hindman168.NativeLieAdjointKernelCenter
import Hindman168.NilpotentBanachExponentialInjective

/-! Equal values of the actual original native exponential have equal
actual adjoint generators. Original group nilpotency supplies the real
nilpotent cutoff, so equality of the genuine adjoint exponentials can be
cancelled without assuming commuting generators or a global logarithm. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_eq_of_exponential_eq {v w : E}
    (h : nativeLieExponential (I := I) (G := G) v =
      nativeLieExponential (I := I) (G := G) w) :
    nativeLieAdjointGenerator (I := I) (G := G) v =
      nativeLieAdjointGenerator (I := I) (G := G) w := by
  apply nilpotent_banach_exp_injective
    ⟨Group.nilpotencyClass G, nativeLieAdjointGenerator_pow_nilpotencyClass v⟩
    ⟨Group.nilpotencyClass G, nativeLieAdjointGenerator_pow_nilpotencyClass w⟩
  rw [← nativeLieAdjoint_exponential_eq_exp, ← nativeLieAdjoint_exponential_eq_exp, h]

 theorem nativeLieAdjointGenerator_sub_eq_zero_of_exponential_eq {v w : E}
    (h : nativeLieExponential (I := I) (G := G) v =
      nativeLieExponential (I := I) (G := G) w) :
    nativeLieAdjointGenerator (I := I) (G := G) (v - w) = 0 := by
  rw [nativeLieAdjointGenerator_eq_differential, map_sub,
    ← nativeLieAdjointGenerator_eq_differential, ← nativeLieAdjointGenerator_eq_differential,
    nativeLieAdjointGenerator_eq_of_exponential_eq h, sub_self]

 theorem nativeLieBracket_eq_zero_of_exponential_eq {v w : GroupLieAlgebra I G}
    (h : nativeLieExponential (I := I) (G := G) v =
      nativeLieExponential (I := I) (G := G) w) : ⁅v, w⁆ = 0 := by
  rw [← nativeLieAdjointGenerator_eq_native_bracket,
    nativeLieAdjointGenerator_eq_of_exponential_eq h, nativeLieAdjointGenerator_self]
  rfl

 theorem nativeLieBracket_sub_eq_zero_of_exponential_eq {v w : GroupLieAlgebra I G}
    (h : nativeLieExponential (I := I) (G := G) v =
      nativeLieExponential (I := I) (G := G) w) (u : GroupLieAlgebra I G) : ⁅v - w, u⁆ = 0 := by
  rw [← nativeLieAdjointGenerator_eq_native_bracket]
  let z : E := v - w
  let q : E := u
  change nativeLieAdjointGenerator (I := I) (G := G) z q = (0 : E)
  have hz : nativeLieAdjointGenerator (I := I) (G := G) z = 0 :=
    nativeLieAdjointGenerator_sub_eq_zero_of_exponential_eq h
  exact congrArg (fun A : E →L[ℝ] E => A q) hz

end Hindman168
