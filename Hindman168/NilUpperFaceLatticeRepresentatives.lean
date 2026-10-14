import Hindman168.NilUpperFaceCoordinates

/-! Ordered representatives modulo the vertexwise lattice. Collection moves
lattice factors to the right by the actual suffix normalizer; the lattice
itself need not be normal. -/

namespace Hindman168
open scoped Classical Pointwise

variable {G : Type*} [Group G] {d : ℕ}

def cubeVertexLattice (Γ : Subgroup G) : Subgroup (Finset (Fin d) → G) where
  carrier := {z | ∀ E, z E ∈ Γ}
  one_mem' _ := Γ.one_mem
  mul_mem' ha hb E := Γ.mul_mem (ha E) (hb E)
  inv_mem' ha E := Γ.inv_mem (ha E)

noncomputable def upperFaceRepresentativeSet (K : ℕ → Set G) :
    List (Finset (Fin d)) → Set (Finset (Fin d) → G)
  | [] => {1}
  | D :: faces => upperFaceArray D '' K D.card * upperFaceRepresentativeSet K faces

def LayerLatticeRepresentatives (F : ℕ → Subgroup G) (Γ : Subgroup G)
    (K : ℕ → Set G) : Prop :=
  (∀ i, K i ⊆ F i) ∧ ∀ i, ∀ g ∈ F i, ∃ k ∈ K i, ∃ γ ∈ Γ, g = k * γ

theorem cubeVertexLattice_upperFace (Γ : Subgroup G) (D : Finset (Fin d))
    (γ : G) (hγ : γ ∈ Γ) : upperFaceArray D γ ∈ cubeVertexLattice Γ := by
  intro E
  by_cases h : D ⊆ E <;> simp [upperFaceArray, h, hγ, Γ.one_mem]

theorem layerLatticeRepresentatives_factor {F : ℕ → Subgroup G} {Γ : Subgroup G}
    {K : ℕ → Set G} (hK : LayerLatticeRepresentatives F Γ K)
    (i : ℕ) (g : G) (hg : g ∈ F i) :
    ∃ k ∈ K i, ∃ γ ∈ F i, γ ∈ Γ ∧ g = k * γ := by
  obtain ⟨k, hk, γ, hγ, heq⟩ := hK.2 i g hg
  refine ⟨k, hk, γ, ?_, hγ, heq⟩
  have hkg := (F i).mul_mem ((F i).inv_mem (hK.1 i hk)) hg
  simpa only [heq, inv_mul_cancel_left] using hkg

theorem upperFaceRepresentativeSet_subset (F : ℕ → Subgroup G) (K : ℕ → Set G)
    (hK : ∀ i, K i ⊆ F i) (faces : List (Finset (Fin d))) :
    upperFaceRepresentativeSet K faces ⊆ upperFaceTailGroup F faces := by
  induction faces with
  | nil =>
    intro z hz
    rcases hz with rfl
    exact (upperFaceTailGroup F []).one_mem
  | cons D faces ih =>
    rintro z ⟨v, ⟨k, hk, rfl⟩, u, hu, rfl⟩
    apply (upperFaceTailGroup F (D :: faces)).mul_mem
    · exact upperFaceTailGroup_generator F (D :: faces) D (by simp) k (hK _ hk)
    · rw [upperFaceTailGroup_cons]
      exact Subgroup.mem_sup_right (ih hu)

theorem upperFaceTailGroup_lattice_representatives (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) (faces : List (Finset (Fin d)))
    (horder : faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E))
    (hclosed : UpperFaceTailClosed faces) (z : Finset (Fin d) → G)
    (hz : z ∈ upperFaceTailGroup F faces) :
    ∃ k ∈ upperFaceRepresentativeSet K faces, ∃ γ ∈ cubeVertexLattice Γ, z = k * γ := by
  induction faces generalizing z with
  | nil =>
    have hz1 : z = 1 := by simpa only [upperFaceTailGroup_nil, Subgroup.mem_bot] using hz
    exact ⟨1, by simp [upperFaceRepresentativeSet], 1,
      (cubeVertexLattice Γ).one_mem, by simpa using hz1⟩
  | cons D faces ih =>
    have htorder := (List.pairwise_cons.mp horder).2
    have htclosed := upperFaceTailClosed_tail D faces horder hclosed
    have hnorm := upperFaceSubgroup_normalizes_tail F hF D faces htclosed
    have hmul : z ∈ (upperFaceSubgroup F D : Set (Finset (Fin d) → G)) *
        (upperFaceTailGroup F faces : Set (Finset (Fin d) → G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
        ← upperFaceTailGroup_cons]
      exact hz
    obtain ⟨v, ⟨g, hg, rfl⟩, u, hu, hvu⟩ := hmul
    obtain ⟨k, hk, γ, hγF, hγΓ, hgk⟩ := layerLatticeRepresentatives_factor hK D.card g hg
    have hγface : upperFaceArray D γ ∈ upperFaceSubgroup F D := ⟨γ, hγF, rfl⟩
    have hu' : upperFaceArray D γ * u * (upperFaceArray D γ)⁻¹ ∈
        upperFaceTailGroup F faces :=
      ((Subgroup.mem_normalizer_iff.mp (hnorm hγface)) u).mp hu
    obtain ⟨k', hk', γ', hγ', hu'factor⟩ := ih htorder htclosed _ hu'
    refine ⟨upperFaceArray D k * k', ?_, γ' * upperFaceArray D γ,
      (cubeVertexLattice Γ).mul_mem hγ' (cubeVertexLattice_upperFace Γ D γ hγΓ), ?_⟩
    · exact ⟨upperFaceArray D k, ⟨k, hk, rfl⟩, k', hk', rfl⟩
    · calc
        z = upperFaceArray D (k * γ) * u := by
          rw [← hgk, ← upperFaceHom_apply]; exact hvu.symm
        _ = upperFaceArray D k *
            (upperFaceArray D γ * u * (upperFaceArray D γ)⁻¹) * upperFaceArray D γ := by
          rw [← upperFaceHom_apply, (upperFaceHom D).map_mul]
          simp [upperFaceHom_apply, mul_assoc]
        _ = (upperFaceArray D k * k') * (γ' * upperFaceArray D γ) := by
          rw [hu'factor]; simp only [mul_assoc]

theorem upperFaceCubeGroup_lattice_representatives (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) (K : ℕ → Set G)
    (hK : LayerLatticeRepresentatives F Γ K) (z : Finset (Fin d) → G)
    (hz : z ∈ upperFaceCubeGroup F d) :
    ∃ k ∈ upperFaceRepresentativeSet K (orderedCubeFaces d),
      ∃ γ ∈ cubeVertexLattice Γ, z = k * γ := by
  apply upperFaceTailGroup_lattice_representatives F hF Γ K hK (orderedCubeFaces d)
    (orderedCubeFaces_pairwise d) (orderedCubeFaces_tailClosed d)
  simpa only [upperFaceCubeGroup_eq_full_tail] using hz

end Hindman168
