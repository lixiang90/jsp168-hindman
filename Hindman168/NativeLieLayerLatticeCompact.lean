import Hindman168.NativeRationalLatticeCompact
import Hindman168.RationalLieLowerCentral

/-! The original real Lie lower-central layers are rational for the
specified lattice's proved rational form. Their genuine exponential
subgroups consequently have compact original lattice-intersection quotients.
This does not identify them with algebraic GROUP lower-central layers. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieLowerCentralModel_lattice_rational
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieLowerCentralModel (I := I) (G := G) j) := by
  let W : Submodule ℚ (GroupLieAlgebra I G) :=
    nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  -- This scalar restriction is only a presentation of W as an additive
  -- integer module. It is NOT Log Gamma and is NOT assumed discrete.
  let L := W.restrictScalars ℤ
  have hQ : span ℚ (L : Set (GroupLieAlgebra I G)) = W :=
    Submodule.span_eq W
  have hR : span ℝ (L : Set (GroupLieAlgebra I G)) = ⊤ :=
    nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ
  have hbr : ∀ x ∈ span ℚ (L : Set (GroupLieAlgebra I G)),
      ∀ y ∈ span ℚ (L : Set (GroupLieAlgebra I G)),
        ⁅x, y⁆ ∈ span ℚ (L : Set (GroupLieAlgebra I G)) := by
    rw [hQ]
    intro x hx y hy
    exact nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ x y hx hy
  have hr := lieLowerCentral_rational L hR hbr j
  unfold RationalLinearSubspace at hr
  rw [hQ] at hr
  exact hr

theorem nativeLieLowerCentralLattice_quotient_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    CompactSpace (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j ⧸
      Γ.comap (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j).subtype) := by
  exact nativeRationalLieLattice_quotient_compact Γ _
    (nativeLieLowerCentralModel_lattice_rational Γ j)

theorem nativeLieLowerCentralLattice_quotient_closedEmbedding
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    Topology.IsClosedEmbedding (subgroupLatticeQuotientInclusion Γ
      (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j)) := by
  exact nativeRationalLieLattice_quotient_closedEmbedding Γ _
    (nativeLieLowerCentralModel_lattice_rational Γ j)

theorem nativeLieLowerCentralLattice_orbit_isCompact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    IsCompact (((↑) : G → G ⧸ Γ) ''
      (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j : Set G)) := by
  exact nativeRationalLieLattice_orbit_isCompact Γ _
    (nativeLieLowerCentralModel_lattice_rational Γ j)

theorem nativeLieLowerCentralLattice_quotient_metrizable
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    TopologicalSpace.MetrizableSpace
      (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j ⧸
        Γ.comap (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j).subtype) := by
  exact nativeRationalLieLattice_quotient_metrizable Γ _
    (nativeLieLowerCentralModel_lattice_rational Γ j)

end Hindman168
