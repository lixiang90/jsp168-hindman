import Hindman168.NativeLieGlobalLogarithm
import Hindman168.NativeLieExponentialCommutingAdd
import Hindman168.NilpotentFiniteExponentialFixedVector

/-! Actual commuting exponentials in the original simply connected
nilpotent Lie group are characterized by the actual native bracket.
Global exponential injectivity and the true finite adjoint formula
prove the reverse implication, with no supplied BCH identity. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_apply_eq_zero_of_exponentials_commute {v w : E}
    (h : Commute (nativeLieExponential (I := I) (G := G) v)
      (nativeLieExponential (I := I) (G := G) w)) :
    nativeLieAdjointGenerator (I := I) (G := G) v w = 0 := by
  have hc := nativeLieAdjoint_curve_conjugation (I := I)
    (nativeLieExponential (I := I) (G := G) v) w 1
  change nativeLieExponential (I := I) (G := G) v *
    nativeLieExponential (I := I) (G := G) w *
      (nativeLieExponential (I := I) (G := G) v)⁻¹ =
    nativeLieExponential (I := I) (G := G)
      (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) w) at hc
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one] at hc
  have hw := nativeLieExponential_injective (I := I) (G := G) hc.symm
  apply nilpotent_finite_exponential_fixed_vector
    (nativeLieAdjointGenerator_pow_nilpotencyClass (I := I) (G := G) v)
  rw [← nativeLieAdjoint_exponential_finite_formula_of_group_isNilpotent]
  exact hw

 theorem nativeLieExponential_commute_iff_generator_apply_eq_zero (v w : E) :
    Commute (nativeLieExponential (I := I) (G := G) v)
      (nativeLieExponential (I := I) (G := G) w) ↔
    nativeLieAdjointGenerator (I := I) (G := G) v w = 0 :=
  ⟨nativeLieAdjointGenerator_apply_eq_zero_of_exponentials_commute,
    fun h => nativeLieCurves_commute_of_generator_apply_eq_zero h 1 1⟩

 theorem nativeLieExponential_commute_iff_bracket_eq_zero (v w : GroupLieAlgebra I G) :
    Commute (nativeLieExponential (I := I) (G := G) v)
      (nativeLieExponential (I := I) (G := G) w) ↔ ⁅v, w⁆ = 0 := by
  rw [nativeLieExponential_commute_iff_generator_apply_eq_zero,
    nativeLieAdjointGenerator_eq_native_bracket]
  rfl

end Hindman168
