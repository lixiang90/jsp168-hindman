import Hindman168.RoughNativeOrbitSourceMetric
import Hindman168.RoughNativeConjugateLatticeCompact
import Hindman168.NativeLieSubalgebraLieGroup

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_orbit_source_metric_quotientMap {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : Subgroup D.G) (g : D.G)
    [CompactSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype)] :
    @IsOpenQuotientMap L (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype)
      inferInstance (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace (↑) := by
  let Δ := (roughConjugateSubgroup D.Γ g).comap L.subtype
  let P (t : TopologicalSpace (L ⧸ Δ)) : Prop :=
    @IsOpenQuotientMap L (L ⧸ Δ) inferInstance t (↑)
  have hn : P (QuotientGroup.instTopologicalSpace Δ) := QuotientGroup.isOpenQuotientMap_mk
  exact Eq.mp (congrArg P (rough_native_orbit_source_metric_topology D L g)) hn

noncomputable def roughNativeSubgroupNilmanifold {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    NativeNilmanifoldData.{u} s := by
  let T := nativeLieSubalgebraModel (E := D.E) S
  let L := nativeLieSubalgebraSubgroup (E := D.E) S
  let g := nativeLieExponential (I := D.I) (G := D.G) v
  let Δ := (roughConjugateSubgroup D.Γ g).comap L.subtype
  letI := nativeLieSubalgebraChartedSpace (E := D.E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := nativeLieSubalgebra_boundaryless S
  letI := nativeLieSubalgebraSubgroup_connected S
  letI := nativeLieSubalgebraSubgroup_simplyConnected S
  letI : Module ℚ T := Module.compHom _ (Rat.castHom ℝ)
  letI := rough_native_conjugate_lattice_intersection_discrete D.Γ g S
  letI := rough_native_conjugate_lattice_quotient_compact D.Γ hv S hS
  exact {
    E := T
    H := T
    I := 𝓘(ℝ, T)
    G := L
    step_le := (Subgroup.nilpotencyClass_le L).trans D.step_le
    Γ := Δ
    metric := roughNativeOrbitSourceMetric D L g
    metric_quotientMap := rough_native_orbit_source_metric_quotientMap D L g }

theorem roughNativeSubgroupNilmanifold_model {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    (roughNativeSubgroupNilmanifold D S hS v hv).E = nativeLieSubalgebraModel (E := D.E) S := rfl

theorem roughNativeSubgroupNilmanifold_group {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    (roughNativeSubgroupNilmanifold D S hS v hv).G = nativeLieSubalgebraSubgroup (E := D.E) S := rfl

theorem roughNativeSubgroupNilmanifold_lattice {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    (roughNativeSubgroupNilmanifold D S hS v hv).Γ =
      (roughConjugateSubgroup D.Γ (nativeLieExponential (I := D.I) (G := D.G) v)).comap
        (nativeLieSubalgebraSubgroup (E := D.E) S).subtype := rfl

end Hindman168
