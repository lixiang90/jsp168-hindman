import Hindman168.CentralPositiveRootSubgroup
import Hindman168.NativeLieCenterModel
import Hindman168.NativeLiePowerRoots

/-! In the actual original simply connected nilpotent Lie group,
a positive natural power is central exactly when the original element
is central. Actual Log(g^n)=n Log(g) and the actual real center model
prove this without assuming root-saturation subgroup closure. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

include I

theorem nativeLie_positive_power_mem_center_iff (g : G) {n : ℕ} (hn : 0 < n) :
    g ^ n ∈ Subgroup.center G ↔ g ∈ Subgroup.center G := by
  rw [← nativeLieGlobalLogarithm_mem_centerModel_iff (I := I) (G := G) (g ^ n),
    nativeLieGlobalLogarithm_pow,
    ← nativeLieGlobalLogarithm_mem_centerModel_iff (I := I) (G := G) g]
  exact smul_mem_iff (nativeLieCenterModel (I := I) (G := G))
    (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))

theorem nativePositiveRoots_center_intersection (Γ : Subgroup G) :
    positiveSubgroupRoots (Γ ⊓ Subgroup.center G) =
      (centralPositiveRootSubgroup Γ : Set G) := by
  ext g
  constructor
  · rintro ⟨n, hn, hgn⟩
    exact ⟨⟨n, hn, hgn.1⟩,
      (nativeLie_positive_power_mem_center_iff (I := I) (G := G) g hn).mp hgn.2⟩
  · rintro ⟨⟨n, hn, hgn⟩, hg⟩
    exact ⟨n, hn, hgn, (Subgroup.center G).pow_mem hg n⟩

end Hindman168
