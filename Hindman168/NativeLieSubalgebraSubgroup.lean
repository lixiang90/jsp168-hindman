import Hindman168.NativeLieSubalgebraPicard
import Hindman168.NativeLieExponentialDiffeomorph

/-! The exponential image of any actual original native Lie subalgebra
is a genuine subgroup of the original group. True finite Picard product
logarithms supply product closure. In the original simply connected case,
the genuine global logarithm gives the exact membership correspondence. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraSubgroup
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) : Subgroup G where
  carrier := (fun v : E => nativeLieExponential (I := I) (G := G) v) ''
    (nativeLieSubalgebraModel S : Set E)
  one_mem' := ⟨0, (nativeLieSubalgebraModel S).zero_mem,
    nativeLieExponential_zero (I := I) (G := G)⟩
  mul_mem' := by
    rintro a b ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1,
      nativeLieLogarithmLift_mem_subalgebra S hu hw 1,
      nativeLieExponential_product_logarithm (E := E) (I := I) (G := G) u w⟩
  inv_mem' := by
    rintro a ⟨u, hu, rfl⟩
    exact ⟨-u, (nativeLieSubalgebraModel S).neg_mem hu,
      nativeLieExponential_neg (I := I) (G := G) u⟩

 theorem nativeLieSubalgebraSubgroup_mem_iff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) :
    g ∈ nativeLieSubalgebraSubgroup (E := E) S ↔
      ∃ v : E, v ∈ nativeLieSubalgebraModel S ∧ nativeLieExponential (I := I) (G := G) v = g :=
  Iff.rfl

 theorem nativeLieSubalgebraSubgroup_eq_generated
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    nativeLieSubalgebraSubgroup (E := E) S =
      Subgroup.closure ((fun v : E => nativeLieExponential (I := I) (G := G) v) ''
        (nativeLieSubalgebraModel S : Set E)) := by
  apply le_antisymm
  · intro g hg
    exact Subgroup.subset_closure hg
  · exact (Subgroup.closure_le (K := nativeLieSubalgebraSubgroup (E := E) S)).mpr (fun _ hg => hg)

variable [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) :
    g ∈ nativeLieSubalgebraSubgroup (E := E) S ↔
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
        nativeLieSubalgebraModel (E := E) S := by
  let V : Submodule ℝ E := nativeLieSubalgebraModel (E := E) S
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  change g ∈ nativeLieSubalgebraSubgroup (E := E) S ↔ log g ∈ V
  constructor
  · rintro ⟨v, hv, rfl⟩
    have he : log (exp v) = v :=
      nativeLieGlobalLogarithm_exponential (E := E) (I := I) (G := G) v
    change log (exp v) ∈ V
    rw [he]
    exact hv
  · intro hg
    exact ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g, hg,
      nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g⟩

end Hindman168
