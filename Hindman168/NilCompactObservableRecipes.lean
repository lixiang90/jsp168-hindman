import Hindman168.NilPieceLinearOrbits

/-! Missing-root recipes for compact continuous observable families.
The domain topology is fixed; no Lipschitz constant is transferred to
an arbitrarily chosen compatible metric. -/

namespace Hindman168
open scoped BigOperators Classical

variable {ι X : Type*}

theorem compactCorner_compactObservable_recipes [Fintype ι] [TopologicalSpace X] [T35Space X] [CompactSpace X]
    (K : Set (Option ι → X)) (hcompact : IsCompact K) (hunique : CornerUnique K)
    (A : Set C(X, ℝ)) (hA : IsCompact A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe ι X), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ c ∈ K, |r.value (cornerDelete c) - f (c none)| < ε) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let vertex : ι → C(K, X) := fun j =>
    ⟨fun x => x.val (some j), (continuous_apply (some j)).comp continuous_subtype_val⟩
  let root : C(K, X) := ⟨fun x => x.val none, (continuous_apply none).comp continuous_subtype_val⟩
  obtain ⟨recipes, C, hC, hb, ha⟩ := cornerRecipe_compact_family vertex
    (cornerDelete_injective_on_cubes K hunique) root A hA ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro c hc
  have hp := happrox ⟨c, hc⟩
  rw [cornerRecipe_eval_eq_value] at hp
  exact hp

variable {G : Type*} [Group G] {d : ℕ}

theorem upperFaceCubeGroup_root_compactObservable_recipes (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] [T35Space (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (A : Set C(G ⧸ Γ, ℝ)) (hA : IsCompact A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (CubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ z ∈ upperFaceCubeGroup F d,
        |r.value (fun E => (z E.val : G ⧸ Γ)) - f (z ∅)| < ε) := by
  obtain ⟨recipes, C, hC, hb, ha⟩ := compactCorner_compactObservable_recipes
    (rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d))
    (rootCosetCornerCubeSet_isCompact Γ _ hcompact)
    (upperFaceCubeGroup_root_corner_unique F hF htop Γ) A hA ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro z hz
  exact happrox (rootCosetCornerCube Γ z) ⟨z, hz, rfl⟩

theorem upperFaceCubeGroup_linear_compactObservable_recipes (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (hzero : F 0 = ⊤) (hone : F 1 = ⊤)
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)] [T35Space (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (A : Set C(G ⧸ Γ, ℝ)) (hA : IsCompact A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (CubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ g x : G, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
        |r.value (fun E => (g ^ (b₀ + ∑ j ∈ E.val, b j) * x : G ⧸ Γ)) - f (g ^ b₀ * x)| < ε) := by
  obtain ⟨recipes, C, hC, hb, ha⟩ := upperFaceCubeGroup_root_compactObservable_recipes
    F hF htop Γ hcompact A hA ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro g x b₀ b
  simpa only [Finset.sum_empty, add_zero] using happrox
    (fun E => g ^ (b₀ + ∑ j ∈ E, b j) * x)
    (upperFace_linear_orbit_cube_mem F hzero hone g x b₀ b)

variable {P : Type*}

theorem upperFaceCubeGroup_piece_compactObservable_recipe_family (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (hzero : F 0 = ⊤) (hone : F 1 = ⊤)
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)] [T35Space (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (obs : P → C(G ⧸ Γ, ℝ)) (H : Set C(G ⧸ Γ, ℝ))
    (hH : IsCompact H) (hobs : ∀ p, obs p ∈ H)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ recipes : Fin N → CornerProductRecipe (CubeVertex d) (G ⧸ Γ),
      ∃ chooseRecipe : P → Fin N, ∃ C : ℝ, 0 ≤ C ∧
      (∀ r, CornerProductRecipe.Bounded (recipes r) ∧ (recipes r).coefficientMass ≤ C) ∧
      ∀ p, ∀ g x : G, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
        |(recipes (chooseRecipe p)).value
          (fun E => (g ^ (b₀ + ∑ j ∈ E.val, b j) * x : G ⧸ Γ)) - obs p (g ^ b₀ * x)| < δ := by
  obtain ⟨rs, C, hC, hb, ha⟩ := upperFaceCubeGroup_linear_compactObservable_recipes F hF htop hzero hone Γ
    hcompact H hH δ hδ
  have hchoose (p : P) := ha (obs p) (hobs p)
  choose selected hselected happrox using hchoose
  have hget (p : P) : ∃ i : Fin rs.toList.length, rs.toList.get i = selected p :=
    List.mem_iff_get.mp (Finset.mem_toList.mpr (hselected p))
  choose index hindex using hget
  refine ⟨rs.toList.length, rs.toList.get, index, C, hC, ?_, ?_⟩
  · intro i
    exact hb _ (Finset.mem_toList.mp (List.get_mem _ _))
  · intro p g x b₀ b
    rw [hindex p]
    exact happrox p g x b₀ b

end Hindman168
