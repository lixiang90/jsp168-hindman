import Hindman168.NilUpperFaceLatticeRepresentatives
import Mathlib.Topology.Algebra.Group.Quotient

/-! Compactness of the actual quotient cube image, derived from compact
representatives at the filtration layers. The quotient continuity premise
is explicit so a metric on the quotient cannot silently change topology. -/

namespace Hindman168
open scoped Classical Pointwise

variable {G : Type*} [Group G] {d : ℕ}

theorem cosetCornerCube_lattice_mul (Γ : Subgroup G) (z γ : Finset (Fin d) → G)
    (hγ : γ ∈ cubeVertexLattice Γ) : cosetCornerCube Γ (z * γ) = cosetCornerCube Γ z := by
  have heq (E : Finset (Fin d)) : ((z E * γ E : G) : G ⧸ Γ) = (z E : G ⧸ Γ) := by
    symm
    apply QuotientGroup.eq.mpr
    simpa only [inv_mul_cancel_left] using hγ E
  funext v
  cases v with
  | none => exact heq Finset.univ
  | some E => exact heq E.val

theorem upperFaceCubeGroup_coset_image_representatives (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) :
    cosetCornerCubeSet Γ (upperFaceCubeGroup F d) =
      cosetCornerCube Γ '' upperFaceRepresentativeSet K (orderedCubeFaces d) := by
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    obtain ⟨k, hk, γ, hγ, rfl⟩ := upperFaceCubeGroup_lattice_representatives F hF Γ K hK z hz
    exact ⟨k, hk, (cosetCornerCube_lattice_mul Γ k γ hγ).symm⟩
  · rintro q ⟨k, hk, rfl⟩
    refine ⟨k, ?_, rfl⟩
    rw [upperFaceCubeGroup_eq_full_tail]
    exact upperFaceRepresentativeSet_subset F K hK.1 _ hk

variable [TopologicalSpace G]

theorem upperFaceArray_continuous (D : Finset (Fin d)) :
    Continuous (upperFaceArray D : G → (Finset (Fin d) → G)) := by
  apply continuous_pi
  intro E
  change Continuous (fun g : G => if D ⊆ E then g else 1)
  by_cases h : D ⊆ E
  · simp only [if_pos h]
    exact continuous_id
  · simp only [if_neg h]
    exact continuous_const

theorem upperFaceRepresentativeSet_isCompact [ContinuousMul G] (K : ℕ → Set G)
    (hK : ∀ i, IsCompact (K i)) (faces : List (Finset (Fin d))) :
    IsCompact (upperFaceRepresentativeSet K faces) := by
  induction faces with
  | nil => exact isCompact_singleton
  | cons D faces ih => exact ((hK D.card).image (upperFaceArray_continuous D)).mul ih

theorem cosetCornerCube_continuous (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) :
    Continuous (cosetCornerCube Γ : (Finset (Fin d) → G) → (Option (ProperCubeVertex d) → G ⧸ Γ)) := by
  apply continuous_pi
  intro v
  cases v with
  | none => exact hπ.comp (continuous_apply Finset.univ)
  | some E => exact hπ.comp (continuous_apply E.val)

theorem upperFaceCubeGroup_coset_isCompact [ContinuousMul G] (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) (hc : ∀ i, IsCompact (K i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  rw [upperFaceCubeGroup_coset_image_representatives F hF Γ K hK]
  exact (upperFaceRepresentativeSet_isCompact K hc _).image (cosetCornerCube_continuous Γ hπ)

theorem upperFaceCubeGroup_quotient_isCompact [ContinuousMul G] (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) (hc : ∀ i, IsCompact (K i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  exact upperFaceCubeGroup_coset_isCompact F hF Γ QuotientGroup.continuous_mk K hK hc

end Hindman168
