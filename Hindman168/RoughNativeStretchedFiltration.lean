import Hindman168.RoughStretchedLowerCentralFiltration
import Hindman168.NativeGroupLowerCentralExact

/-! Identifies the stretched group layers with the original exponential Lie
layers; their topology and logarithmic membership are consequences of this
proved equality, rather than additional filtration hypotheses. -/

namespace Hindman168
open Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_stretched_filtration_eq (D i : ℕ) :
    roughStretchedLowerCentralFiltration G D i =
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) ((i ⌈/⌉ D)-1) :=
  nativeGroupLowerCentralSeries_eq_exponential _

include I in
theorem rough_native_stretched_filtration_closed (D i : ℕ) :
    IsClosed (roughStretchedLowerCentralFiltration G D i : Set G) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralSubgroup_closed _

include I in
theorem rough_native_stretched_filtration_contractible (D i : ℕ) :
    ContractibleSpace (roughStretchedLowerCentralFiltration G D i) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralSubgroup_contractible _

include I in
theorem rough_native_stretched_filtration_simplyConnected (D i : ℕ) :
    SimplyConnectedSpace (roughStretchedLowerCentralFiltration G D i) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralSubgroup_simplyConnected _

theorem rough_native_stretched_filtration_mem_log_iff (D i : ℕ) (g : G) :
    g ∈ roughStretchedLowerCentralFiltration G D i ↔
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
        nativeLieLowerCentralModel (E := E) (I := I) (G := G) ((i ⌈/⌉ D)-1) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralSubgroup_mem_globalLogarithm_iff _ _

theorem rough_native_stretched_filtration_exp_mem_iff (D i : ℕ) (v : E) :
    nativeLieExponential (I := I) (G := G) v ∈ roughStretchedLowerCentralFiltration G D i ↔
      v ∈ nativeLieLowerCentralModel (I := I) (G := G) ((i ⌈/⌉ D)-1) := by
  rw [rough_native_stretched_filtration_mem_log_iff (I := I),
    nativeLieGlobalLogarithm_exponential]

end Hindman168
