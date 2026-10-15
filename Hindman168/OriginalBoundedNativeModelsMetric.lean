import Hindman168.OriginalBoundedNativeModels
import Hindman168.NativeNilmanifoldData

/-! Genuine native models and quantitative observable transport. The metric
is exactly the upstream BCH quotient metric, with its proved quotient topology. -/

namespace Hindman168.OriginalBoundedNativeModels

open Module OAI.Erdos3
open scoped TensorProduct NNReal Manifold ContDiff

section NativeRealization

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

/-- The upstream realification, specified lattice and specified metric,
packaged as the genuine native nilmanifold required by the original theorem. -/
noncomputable def nativeModel : NativeNilmanifoldData.{0} s := by
  letI : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) :=
    (D.basis.baseChange ℝ).finiteDimensional_of_finite
  letI := NilpotentLieBCHGroup.basisChartedSpace
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  letI := NilpotentLieBCHGroup.lieGroup_basis
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) ∞
  letI : Group.IsNilpotent D.RealGroup := D.filtration.realification.isNilpotentGroup
  letI : DiscreteTopology D.realLattice := D.realLattice_closed_discrete.2.to_subtype
  letI : CompactSpace D.Space := D.space_compact
  exact {
    E := Fin d → ℝ
    H := Fin d → ℝ
    I := 𝓘(ℝ, Fin d → ℝ)
    G := D.RealGroup
    step_le := D.filtration.realification.nilpotencyClass_le
    Γ := D.realLattice
    metric := D.metricSpace
    metric_quotientMap := QuotientGroup.isOpenQuotientMap_mk }

end NativeRealization

end Hindman168.OriginalBoundedNativeModels
