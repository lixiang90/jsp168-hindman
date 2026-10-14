import Hindman168.NativeLieCenterExponential
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Topology.Constructions

/-! In the actual original center, the specified subgroup logarithms
form a genuine integer submodule. Addition and negation closure use the
true central exponential laws. Original lattice discreteness transfers
through the actual continuous injective exponential map. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterLogLattice (Γ : Subgroup G) :
    Submodule ℤ (nativeLieCenterModel (I := I) (G := G)) :=
  AddSubgroup.toIntSubmodule {
    carrier := {v | nativeLieExponential (I := I) (G := G) v.val ∈ Γ}
    zero_mem' := by
      change nativeLieExponential (I := I) (G := G) (0 : E) ∈ Γ
      exact (congrArg (fun g : G => g ∈ Γ)
        (nativeLieExponential_zero (I := I) (G := G))).mpr Γ.one_mem
    add_mem' := by
      intro v w hv hw
      change nativeLieExponential (I := I) (G := G) (v.val + w.val) ∈ Γ
      rw [nativeLieExponential_add_of_mem_centerModel v.property]
      exact Γ.mul_mem hv hw
    neg_mem' := by
      intro v hv
      change nativeLieExponential (I := I) (G := G) (-v.val) ∈ Γ
      exact (congrArg (fun g : G => g ∈ Γ)
        (nativeLieExponential_neg (I := I) (G := G) v.val)).mpr (Γ.inv_mem hv)
  }

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G]
  [SimplyConnectedSpace G] in
 theorem nativeCenterLogLattice_mem_iff (Γ : Subgroup G)
    (v : nativeLieCenterModel (I := I) (G := G)) :
    v ∈ nativeCenterLogLattice (I := I) Γ ↔ nativeLieExponential (I := I) (G := G) v.val ∈ Γ :=
  Iff.rfl

 theorem nativeCenterLogLattice_logarithm_mem_iff (Γ : Subgroup G) (g : Subgroup.center G) :
    (nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm g ∈
      nativeCenterLogLattice (I := I) Γ ↔ (g : G) ∈ Γ := by
  change nativeLieExponential (I := I) (G := G)
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g.val) ∈ Γ ↔ g.val ∈ Γ
  rw [nativeLieExponential_globalLogarithm]

 theorem nativeCenterLogLattice_discrete (Γ : Subgroup G) [DiscreteTopology Γ] :
    DiscreteTopology (nativeCenterLogLattice (I := I) Γ) := by
  let f : nativeCenterLogLattice (I := I) Γ → Γ := fun v =>
    ⟨nativeLieExponential (I := I) (G := G) v.val.val, v.property⟩
  have hf : Continuous f := by
    exact (((nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  have hi : Injective f := by
    intro v w he
    have hvw := nativeLieExponential_injective (I := I) (G := G)
      (congrArg (fun γ : Γ => (γ : G)) he)
    exact Subtype.ext (Subtype.ext hvw)
  exact DiscreteTopology.of_continuous_injective hf hi

end Hindman168
