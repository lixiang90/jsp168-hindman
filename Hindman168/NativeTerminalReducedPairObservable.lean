import Hindman168.NativeTerminalRelativePairTranslation
import Hindman168.NativeRelativeReductionProjection
import Hindman168.CentralSubgroupFactorObservable

/-! SAME ACTUAL relative translated terminal pair descends continuously
to SAME actual reduced terminal quotient, retaining all original points. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeTerminalReducedPairObservable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_relative_terminal_subgroup_normal D d hd
  intro F
  exact centralSubgroupFactorObservable (nativeRelativeTerminalSubgroup D d hd)
    (nativeRelativeSquareData D d hd 1).Γ (native_relative_internal_terminal_le_center D d hd)
    (nativeTerminalRelativePairObservable D d hd k g F) (native_terminal_relative_pair_subgroup_invariant D d hd k g F)

theorem native_terminal_reduced_pair_observable_apply {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ),
      nativeTerminalReducedPairObservable D d hd k g F (nativeRelativeReductionFactorMap D d hd q) =
        nativeTerminalRelativePairObservable D d hd k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_relative_terminal_subgroup_normal D d hd
  intro F q
  exact central_subgroup_factor_observable_apply _ _ _ _ _ q

theorem native_terminal_reduced_pair_observable_unique {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (H : C((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,ℂ)),
      (∀ q, H (nativeRelativeReductionFactorMap D d hd q) = nativeTerminalRelativePairObservable D d hd k g F q) →
        H = nativeTerminalReducedPairObservable D d hd k g F := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_relative_terminal_subgroup_normal D d hd
  intro F H hH
  exact central_subgroup_factor_observable_unique _ _ _ _ _ H hH

theorem native_terminal_reduced_pair_unit_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      ∀ q : (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ,
        ‖nativeTerminalReducedPairObservable D d hd k g F q‖ ≤ 1 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := native_relative_terminal_subgroup_normal D d hd
  intro F hF q
  exact central_subgroup_factor_observable_bound _ _ _ _ _ 1
    (native_terminal_relative_pair_unit_bound D d hd k g F hF) q

end Hindman168
