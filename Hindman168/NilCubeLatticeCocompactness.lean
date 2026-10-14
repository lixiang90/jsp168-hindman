import Hindman168.NilFiltrationCompactQuotients

/-! The actual cube subgroup modulo its intersection with the vertexwise
lattice is compact. This proves cocompactness inside the cube subgroup,
in addition to compactness of its image in the ambient vertex quotient. -/

namespace Hindman168
open scoped Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}

noncomputable def upperFaceCubeLattice (F : ℕ → Subgroup G) (Γ : Subgroup G) (d : ℕ) :
    Subgroup (upperFaceCubeGroup F d) :=
  (cubeVertexLattice Γ).comap (upperFaceCubeGroup F d).subtype

theorem upperFaceCube_compact_lattice_representatives (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) (hc : ∀ i, IsCompact (K i)) :
    ∃ S : Set (upperFaceCubeGroup F d), IsCompact S ∧
      ∀ z : upperFaceCubeGroup F d, ∃ k ∈ S, ∃ γ ∈ upperFaceCubeLattice F Γ d, z = k * γ := by
  let R := upperFaceRepresentativeSet K (orderedCubeFaces d)
  have hRH : R ⊆ (upperFaceCubeGroup F d : Set (Finset (Fin d) → G)) := by
    rw [upperFaceCubeGroup_eq_full_tail]
    exact upperFaceRepresentativeSet_subset F K hK.1 _
  let S : Set (upperFaceCubeGroup F d) := Subtype.val ⁻¹' R
  refine ⟨S, ?_, ?_⟩
  · apply Topology.IsInducing.subtypeVal.isCompact_preimage'
      (upperFaceRepresentativeSet_isCompact K hc _)
    simpa only [Subtype.range_val] using hRH
  · intro z
    obtain ⟨k, hk, γ, hγ, heq⟩ := upperFaceCubeGroup_lattice_representatives F hF Γ K hK z.val z.property
    have hkH : k ∈ upperFaceCubeGroup F d := hRH hk
    have hγH : γ ∈ upperFaceCubeGroup F d := by
      have h := (upperFaceCubeGroup F d).mul_mem
        ((upperFaceCubeGroup F d).inv_mem hkH) z.property
      simpa only [heq, inv_mul_cancel_left] using h
    refine ⟨⟨k, hkH⟩, hk, ⟨γ, hγH⟩, hγ, ?_⟩
    exact Subtype.ext heq

theorem upperFaceCubeLattice_compactSpace (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) (hc : ∀ i, IsCompact (K i)) :
    CompactSpace ((upperFaceCubeGroup F d) ⧸ upperFaceCubeLattice F Γ d) := by
  obtain ⟨S, hS, hrep⟩ := upperFaceCube_compact_lattice_representatives F hF Γ K hK hc
  exact compactSpace_of_lattice_representatives _ S hS hrep

theorem upperFaceCubeLattice_compactSpace_from_layer_quotients (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G)
    (hloc : ∀ i, WeaklyLocallyCompactSpace (F i))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    CompactSpace ((upperFaceCubeGroup F d) ⧸ upperFaceCubeLattice F Γ d) := by
  obtain ⟨K, hK, hc⟩ := filtration_compact_lattice_representatives F Γ hloc hquot
  exact upperFaceCubeLattice_compactSpace F hF Γ K hK hc

end Hindman168
