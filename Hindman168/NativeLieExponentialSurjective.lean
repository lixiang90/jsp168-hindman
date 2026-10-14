import Hindman168.NativeLieExponentialProductLog
import Hindman168.NativeLieExponentialLocalHomeomorph
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

/-! The actual original exponential range is an open subgroup: the true
finite Picard curve supplies a logarithm of every product. Connectedness
of the original group then proves genuine whole-group surjectivity. No
surjectivity or global inverse is supplied as an extra hypothesis. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieExponentialRangeSubgroup : Subgroup G where
  carrier := Set.range (nativeLieExponential (I := I) (G := G) : E → G)
  one_mem' := ⟨0, nativeLieExponential_zero (I := I) (G := G)⟩
  mul_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨w, rfl⟩
    exact ⟨nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1,
      nativeLieExponential_product_logarithm (E := E) (I := I) (G := G) u w⟩
  inv_mem' := by
    rintro a ⟨u, rfl⟩
    exact ⟨-u, nativeLieExponential_neg (I := I) (G := G) u⟩

 theorem nativeLieExponential_range_eq_univ [ConnectedSpace G] :
    Set.range (nativeLieExponential (I := I) (G := G) : E → G) = univ := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let S : Subgroup G := nativeLieExponentialRangeSubgroup (E := E) (I := I) (G := G)
  have ho : IsOpen (S : Set G) := nativeLieExponential_range_open (I := I) (G := G)
  have hc : IsClopen (S : Set G) := ⟨S.isClosed_of_isOpen ho, ho⟩
  exact hc.eq_univ ⟨1, S.one_mem⟩

 theorem nativeLieExponential_surjective [ConnectedSpace G] :
    Surjective (nativeLieExponential (I := I) (G := G) : E → G) :=
  Set.range_eq_univ.mp (nativeLieExponential_range_eq_univ (I := I) (G := G))

end Hindman168
