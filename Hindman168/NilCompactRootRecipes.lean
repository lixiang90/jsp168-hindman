import Hindman168.NilFiltrationCompactQuotients
import Hindman168.NilUpperFaceRootRecipes

/-! Prediction's actual root recipes now follow from closed filtration
layers with compact restricted-lattice quotients, rather than an assumed
compact cube image. Quotient metric compatibility remains explicit. -/

namespace Hindman168
open scoped BigOperators Classical
open NNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] {d : ℕ}

omit [IsTopologicalGroup G] in
theorem closedFiltrationLayers_weaklyLocallyCompact (F : ℕ → Subgroup G)
    (hc : ∀ i, IsClosed (F i : Set G)) : ∀ i, WeaklyLocallyCompactSpace (F i) := by
  intro i
  exact (hc i).weaklyLocallyCompactSpace

theorem upperFaceCubeGroup_compact_from_closed_layers (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) (hc : ∀ i, IsClosed (F i : Set G))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  exact upperFaceCubeGroup_compact_from_layer_quotients F hF Γ hπ
    (closedFiltrationLayers_weaklyLocallyCompact F hc) hquot

theorem upperFaceCubeGroup_root_compact_from_closed_layers (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) (hc : ∀ i, IsClosed (F i : Set G))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    IsCompact (rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  exact rootCosetCornerCubeSet_isCompact Γ _
    (upperFaceCubeGroup_compact_from_closed_layers F hF Γ hπ hc hquot)

theorem upperFaceCubeGroup_root_reconstruction_from_closed_layers (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)]
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) (hc : ∀ i, IsClosed (F i : Set G))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i)) :
    ∃ R : C(Set.range (fun x : rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d) =>
      cornerDelete x.val), G ⧸ Γ),
      ∀ x : rootCosetCornerCubeSet Γ (upperFaceCubeGroup F d),
        R ⟨cornerDelete x.val, ⟨x, rfl⟩⟩ = x.val none := by
  exact upperFaceCubeGroup_root_continuous_reconstruction F hF htop Γ
    (upperFaceCubeGroup_compact_from_closed_layers F hF Γ hπ hc hquot)

section MetricQuotient
variable (Γ : Subgroup G) [qMetric : MetricSpace (G ⧸ Γ)]
local instance metricQuotientTopology : TopologicalSpace (G ⧸ Γ) := qMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable [CompactSpace (G ⧸ Γ)]

theorem upperFaceCubeGroup_root_recipes_from_closed_layers (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥)
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) (hc : ∀ i, IsClosed (F i : Set G))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i))
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L (fun x : G ⧸ Γ => f x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (CubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ z ∈ upperFaceCubeGroup F d,
        |r.value (fun E => (z E.val : G ⧸ Γ)) - f (z ∅)| < ε) := by
  exact upperFaceCubeGroup_root_boundedLipschitz_recipes F hF htop Γ
    (upperFaceCubeGroup_compact_from_closed_layers F hF Γ hπ hc hquot) A B L hB hL ε hε

theorem upperFaceCubeGroup_linear_recipes_from_closed_layers (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (hzero : F 0 = ⊤) (hone : F 1 = ⊤)
    (hπ : Continuous ((↑) : G → G ⧸ Γ)) (hc : ∀ i, IsClosed (F i : Set G))
    (hquot : ∀ i, CompactSpace ((F i) ⧸ filtrationLayerLattice F Γ i))
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L (fun x : G ⧸ Γ => f x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (CubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ g x : G, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
        |r.value (fun E => (g ^ (b₀ + ∑ j ∈ E.val, b j) * x : G ⧸ Γ)) - f (g ^ b₀ * x)| < ε) := by
  exact upperFaceCubeGroup_linear_root_recipes F hF htop hzero hone Γ
    (upperFaceCubeGroup_compact_from_closed_layers F hF Γ hπ hc hquot) A B L hB hL ε hε

end MetricQuotient

end Hindman168
