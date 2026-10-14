import Hindman168.NativeCentralSubspaceSubgroup
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Topology.Constructions

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceLogLattice (Γ : Subgroup G) (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) : Submodule ℤ V :=
  AddSubgroup.toIntSubmodule {
    carrier := {v | nativeLieExponential (I := I) (G := G) v.val ∈ Γ}
    zero_mem' := by
      change nativeLieExponential (I := I) (G := G) (0 : E) ∈ Γ
      exact (congrArg (fun g : G => g ∈ Γ)
        (nativeLieExponential_zero (I := I) (G := G))).mpr Γ.one_mem
    add_mem' := by
      intro v w hv hw
      change nativeLieExponential (I := I) (G := G) (v.val+w.val) ∈ Γ
      rw [nativeLieExponential_add_of_mem_centerModel (hV v.property)]
      exact Γ.mul_mem hv hw
    neg_mem' := by
      intro v hv
      change nativeLieExponential (I := I) (G := G) (-v.val) ∈ Γ
      exact (congrArg (fun g : G => g ∈ Γ)
        (nativeLieExponential_neg (I := I) (G := G) v.val)).mpr (Γ.inv_mem hv)
  }

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G]
  [SimplyConnectedSpace G] in
theorem nativeCentralSubspaceLogLattice_mem_iff (Γ : Subgroup G) (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (v : V) :
    v ∈ nativeCentralSubspaceLogLattice (I := I) Γ V hV ↔
      nativeLieExponential (I := I) (G := G) v.val ∈ Γ := Iff.rfl

theorem nativeCentralSubspaceLogLattice_discrete (Γ : Subgroup G) [DiscreteTopology Γ]
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    DiscreteTopology (nativeCentralSubspaceLogLattice (I := I) Γ V hV) := by
  let f : nativeCentralSubspaceLogLattice (I := I) Γ V hV → Γ := fun v =>
    ⟨nativeLieExponential (I := I) (G := G) v.val.val, v.property⟩
  have hf : Continuous f :=
    (((nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  have hi : Injective f := by
    intro v w he
    have h := nativeLieExponential_injective (I := I) (G := G)
      (congrArg (fun γ : Γ => (γ : G)) he)
    exact Subtype.ext (Subtype.ext h)
  exact DiscreteTopology.of_continuous_injective hf hi

end Hindman168
