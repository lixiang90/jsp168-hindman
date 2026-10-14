import Hindman168.CompactQuotientRepresentatives
import Hindman168.NilUpperFaceCompactness

/-! Compact representatives for every filtration layer are derived from
its actual compact quotient by the restricted lattice. This reduces cube
compactness to the rational-layer cocompactness used in the paper. -/

namespace Hindman168
open scoped Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def filtrationLayerLattice (F : ℕ → Subgroup G) (Γ : Subgroup G) (i : ℕ) :
    Subgroup (F i) := Γ.comap (F i).subtype

theorem filtrationLayer_compact_representatives (F : ℕ → Subgroup G) (Γ : Subgroup G)
    (i : ℕ) [WeaklyLocallyCompactSpace (F i)]
    [CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)] :
    ∃ K : Set G, IsCompact K ∧ K ⊆ F i ∧
      ∀ g ∈ F i, ∃ k ∈ K, ∃ γ ∈ Γ, g = k * γ := by
  obtain ⟨K, hc, hrep⟩ := compactQuotient_lattice_representatives (filtrationLayerLattice F Γ i)
  refine ⟨Subtype.val '' K, hc.image continuous_subtype_val, ?_, ?_⟩
  · rintro k ⟨a, _, rfl⟩
    exact a.property
  · intro g hg
    obtain ⟨k, hk, γ, hγ, heq⟩ := hrep ⟨g, hg⟩
    refine ⟨k.val, ⟨k, hk, rfl⟩, γ.val, hγ, ?_⟩
    exact congrArg Subtype.val heq

theorem filtration_compact_lattice_representatives (F : ℕ → Subgroup G) (Γ : Subgroup G)
    (hloc : ∀ i, WeaklyLocallyCompactSpace (F i))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    ∃ K : ℕ → Set G, LayerLatticeRepresentatives F Γ K ∧ ∀ i, IsCompact (K i) := by
  have h (i : ℕ) : ∃ K : Set G, IsCompact K ∧ K ⊆ F i ∧
      ∀ g ∈ F i, ∃ k ∈ K, ∃ γ ∈ Γ, g = k * γ := by
    letI := hloc i
    letI := hquot i
    exact filtrationLayer_compact_representatives F Γ i
  choose K hc hF hrep using h
  exact ⟨K, ⟨hF, hrep⟩, hc⟩

theorem upperFaceCubeGroup_compact_from_layer_quotients {d : ℕ}
    (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F) (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] (hπ : Continuous ((↑) : G → G ⧸ Γ))
    (hloc : ∀ i, WeaklyLocallyCompactSpace (F i))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  obtain ⟨K, hK, hc⟩ := filtration_compact_lattice_representatives F Γ hloc hquot
  exact upperFaceCubeGroup_coset_isCompact F hF Γ hπ K hK hc

theorem upperFaceCubeGroup_natural_compact_from_layer_quotients {d : ℕ}
    (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F) (Γ : Subgroup G)
    (hloc : ∀ i, WeaklyLocallyCompactSpace (F i))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  exact upperFaceCubeGroup_compact_from_layer_quotients F hF Γ
    QuotientGroup.continuous_mk hloc hquot

end Hindman168
