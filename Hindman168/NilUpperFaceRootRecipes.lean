import Hindman168.NilUpperFaceRootUniqueness
import Hindman168.ReplicaCubeRows

/-! The actual root-indexed Boolean cube used by Prediction. Compactness
transfers from the top-indexed quotient cube image by continuous vertex
reindexing. Coordinate certificates and reflection invariance are now
proved, so only actual compactness remains in the root recipe interface. -/

namespace Hindman168
open scoped BigOperators Classical
open NNReal

variable {G : Type*} [Group G] {d : ℕ}

def cubeRootVertex : Option (CubeVertex d) → Finset (Fin d)
  | none => ∅
  | some E => E.val

noncomputable def cubeTopIndex (E : Finset (Fin d)) : Option (ProperCubeVertex d) :=
  if h : E = Finset.univ then none else some ⟨E, h⟩

noncomputable def topCubeToRoot {X : Type*} (c : Option (ProperCubeVertex d) → X) :
    Option (CubeVertex d) → X := fun v => c (cubeTopIndex (cubeRootVertex v))

noncomputable def rootCosetCornerCube (Γ : Subgroup G) (z : Finset (Fin d) → G) :
    Option (CubeVertex d) → G ⧸ Γ := fun v => (z (cubeRootVertex v) : G ⧸ Γ)

noncomputable def rootCosetCornerCubeSet (Γ : Subgroup G)
    (H : Subgroup (Finset (Fin d) → G)) : Set (Option (CubeVertex d) → G ⧸ Γ) :=
  rootCosetCornerCube Γ '' (H : Set (Finset (Fin d) → G))

theorem cubeTopIndex_evaluation (Γ : Subgroup G) (z : Finset (Fin d) → G)
    (E : Finset (Fin d)) : cosetCornerCube Γ z (cubeTopIndex E) = (z E : G ⧸ Γ) := by
  by_cases h : E = Finset.univ
  · subst E; simp [cubeTopIndex, cosetCornerCube]
  · simp [cubeTopIndex, cosetCornerCube, h]

theorem topCubeToRoot_coset (Γ : Subgroup G) (z : Finset (Fin d) → G) :
    topCubeToRoot (cosetCornerCube Γ z) = rootCosetCornerCube Γ z := by
  funext v
  exact cubeTopIndex_evaluation Γ z (cubeRootVertex v)

theorem topCubeToRoot_continuous {X : Type*} [TopologicalSpace X] :
    Continuous (topCubeToRoot (d := d) (X := X)) := by
  exact continuous_pi (fun v => continuous_apply (cubeTopIndex (cubeRootVertex v)))

theorem rootCosetCornerCubeSet_eq_image (Γ : Subgroup G)
    (H : Subgroup (Finset (Fin d) → G)) :
    rootCosetCornerCubeSet Γ H = topCubeToRoot '' cosetCornerCubeSet Γ H := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨cosetCornerCube Γ z, ⟨z, hz, rfl⟩, topCubeToRoot_coset Γ z⟩
  · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (topCubeToRoot_coset Γ z).symm⟩

theorem rootCosetCornerCubeSet_isCompact (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (H : Subgroup (Finset (Fin d) → G)) (hcompact : IsCompact (cosetCornerCubeSet Γ H)) :
    IsCompact (rootCosetCornerCubeSet Γ H) := by
  rw [rootCosetCornerCubeSet_eq_image]
  exact hcompact.image topCubeToRoot_continuous

theorem upperFaceCubeGroup_root_corner_unique (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G) :
    CornerUnique (rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  intro x hx y hy hpartial
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  apply upperFaceCubeGroup_coset_missing_root F hF htop Γ a b ha hb
  intro E hE
  exact hpartial ⟨E, hE⟩

theorem upperFaceCubeGroup_root_continuous_reconstruction (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d))) :
    ∃ R : C(Set.range (fun x : rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d) =>
      cornerDelete x.val), G ⧸ Γ),
      ∀ x : rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d),
        R ⟨cornerDelete x.val, ⟨x, rfl⟩⟩ = x.val none := by
  exact compactCorner_continuous_reconstruction _
    (rootCosetCornerCubeSet_isCompact Γ _ hcompact)
    (upperFaceCubeGroup_root_corner_unique F hF htop Γ)

theorem upperFaceCubeGroup_root_boundedLipschitz_recipes (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (CubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ z ∈ upperFaceCubeGroup F d,
        |r.value (fun E => (z E.val : G ⧸ Γ)) - f (z ∅)| < ε) := by
  obtain ⟨recipes, C, hC, hb, ha⟩ := compactCorner_boundedLipschitz_recipes
    (rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d))
    (rootCosetCornerCubeSet_isCompact Γ _ hcompact)
    (upperFaceCubeGroup_root_corner_unique F hF htop Γ) A B L hB hL ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro z hz
  exact happrox (rootCosetCornerCube Γ z) ⟨z, hz, rfl⟩

theorem upperFaceCubeGroup_linear_root_recipes (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (hzero : F 0 = ⊤) (hone : F 1 = ⊤)
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (CubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ g x : G, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
        |r.value (fun E => (g ^ (b₀ + ∑ j ∈ E.val, b j) * x : G ⧸ Γ)) - f (g ^ b₀ * x)| < ε) := by
  obtain ⟨recipes, C, hC, hb, ha⟩ := upperFaceCubeGroup_root_boundedLipschitz_recipes
    F hF htop Γ hcompact A B L hB hL ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro g x b₀ b
  simpa only [Finset.sum_empty, add_zero] using happrox
    (fun E => g ^ (b₀ + ∑ j ∈ E, b j) * x)
    (upperFace_linear_orbit_cube_mem F hzero hone g x b₀ b)

end Hindman168
