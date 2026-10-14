import Hindman168.NativeRationalCompactRepresentatives
import Hindman168.CompactQuotientRepresentatives
import Hindman168.SubgroupLatticeQuotient
import Hindman168.NilNaturalCosetMetric

/-! Cocompactness and embedded compact orbits for arbitrary original
Gamma-rational native Lie subgroups, with their ACTUAL Gamma intersections. -/

namespace Hindman168
open Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeRationalLieLattice_quotient_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    CompactSpace (nativeLieSubalgebraSubgroup (E := E) S ⧸
      Γ.comap (nativeLieSubalgebraSubgroup (E := E) S).subtype) := by
  obtain ⟨K, hK, hsub, hrep⟩ := nativeRationalLieSubalgebra_compact_representatives Γ S hS
  let L := nativeLieSubalgebraSubgroup (E := E) S
  let KL : Set L := ((↑) : L → G) ⁻¹' K
  have hKR : K ⊆ range ((↑) : L → G) := fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩
  have hKL : IsCompact KL := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKR
  apply compactSpace_of_lattice_representatives (Γ.comap L.subtype) KL hKL
  intro g
  obtain ⟨x, hx, γ, hγ, heq⟩ := hrep g.val g.property
  have hγL : γ ∈ L := by
    have he : γ = x⁻¹ * g.val := by rw [heq]; simp only [inv_mul_cancel_left]
    rw [he]
    exact L.mul_mem (L.inv_mem (hsub hx)) g.property
  exact ⟨⟨x, hsub hx⟩, hx, ⟨γ, hγL⟩, hγ, Subtype.ext heq⟩

theorem nativeRationalLieLattice_quotient_closedEmbedding
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    IsClosedEmbedding (subgroupLatticeQuotientInclusion Γ (nativeLieSubalgebraSubgroup (E := E) S)) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  letI : IsClosed (Γ : Set G) := discreteLattice_isClosed Γ
  letI := nativeRationalLieLattice_quotient_compact Γ S hS
  exact subgroupLatticeQuotientInclusion_closedEmbedding _ _

theorem nativeRationalLieLattice_orbit_isCompact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    IsCompact (((↑) : G → G ⧸ Γ) '' (nativeLieSubalgebraSubgroup (E := E) S : Set G)) := by
  letI := nativeRationalLieLattice_quotient_compact Γ S hS
  exact subgroupLatticeOrbit_isCompact _ _

omit [Module ℚ E] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieLattice_intersection_discrete
    (Γ : Subgroup G) [DiscreteTopology Γ]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    DiscreteTopology (Γ.comap (nativeLieSubalgebraSubgroup (E := E) S).subtype) := by
  let L := nativeLieSubalgebraSubgroup (E := E) S
  let f : Γ.comap L.subtype → Γ := fun g => ⟨g.val.val, g.property⟩
  have h1 : IsEmbedding ((↑) : Γ.comap L.subtype → L) := IsEmbedding.subtypeVal
  have h2 : IsEmbedding ((↑) : L → G) := IsEmbedding.subtypeVal
  have h3 : IsEmbedding ((↑) : Γ → G) := IsEmbedding.subtypeVal
  have hf : IsEmbedding f := h3.of_comp_iff.mp (h2.comp h1)
  exact hf.discreteTopology

theorem nativeRationalLieLattice_quotient_metrizable
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    TopologicalSpace.MetrizableSpace (nativeLieSubalgebraSubgroup (E := E) S ⧸
      Γ.comap (nativeLieSubalgebraSubgroup (E := E) S).subtype) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  let L := nativeLieSubalgebraSubgroup (E := E) S
  letI : SecondCountableTopology L :=
    (nativeLieSubalgebraExponentialHomeomorph (E := E) S).symm.secondCountableTopology
  letI := nativeLieLattice_intersection_discrete Γ S
  letI := nativeRationalLieLattice_quotient_compact Γ S hS
  exact compactDiscreteCosetQuotient_metrizable (Γ.comap L.subtype)

end Hindman168
