import Hindman168.NilUpperFaceCoordinates

/-! The actual filtered cube group in a dimension whose top layer is
trivial satisfies the previous proper-coordinate certificate. Thus its
quotient missing-corner uniqueness no longer requires that certificate
as an independent assumption. Rational compactness remains explicit. -/

namespace Hindman168
open scoped Classical
open NNReal

variable {G : Type*} [Group G] {d : ℕ}

theorem upperFaceArray_one (D : Finset (Fin d)) : upperFaceArray D (1 : G) = 1 := by
  exact (upperFaceHom D).map_one

theorem upperFaceProduct_filter_top (a : Finset (Fin d) → G)
    (faces : List (Finset (Fin d))) (htop : a Finset.univ = 1) :
    upperFaceProduct a (faces.filter (fun D => D ≠ Finset.univ)) = upperFaceProduct a faces := by
  induction faces with
  | nil => rfl
  | cons D faces ih =>
    by_cases hD : D = Finset.univ
    · subst D
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, upperFaceProduct_cons, htop, upperFaceArray_one, one_mul]
      exact ih
    · simp only [List.filter_cons, hD, ne_eq, not_false_eq_true, decide_true,
        if_true, upperFaceProduct_cons]
      rw [ih]

theorem upperFaceCubeGroup_proper_coordinates (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥)
    (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d) :
    ProperUpperFaceCoordinates z := by
  obtain ⟨a, ha, hcoord⟩ := upperFaceCubeGroup_coordinates F hF z hz
  have hatop : a Finset.univ = 1 := by
    have hp := ha Finset.univ
    simpa only [Finset.card_univ, Fintype.card_fin, htop, Subgroup.mem_bot] using hp
  let faces := (orderedCubeFaces d).filter (fun D => D ≠ Finset.univ)
  refine ⟨a, faces, ?_, (orderedCubeFaces_pairwise d).filter _, ?_⟩
  · intro D hD
    exact of_decide_eq_true (List.mem_filter.mp hD).2
  · intro E
    calc
      z E = upperFaceProduct a (orderedCubeFaces d) E := by rw [upperFaceProduct_apply, hcoord E]
      _ = upperFaceProduct a faces E :=
        congrFun (upperFaceProduct_filter_top a (orderedCubeFaces d) hatop).symm E
      _ = upperFaceValue a faces E := upperFaceProduct_apply a faces E

theorem upperFaceCubeGroup_coset_corner_unique (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G) :
    CornerUnique (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)) := by
  exact cosetCornerCubeSet_unique Γ (upperFaceCubeGroup F d)
    (upperFaceCubeGroup_proper_coordinates F hF htop)

theorem upperFaceCubeGroup_continuous_corner_reconstruction (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d))) :
    ∃ R : C(Set.range (fun x : cosetCornerCubeSet Γ (upperFaceCubeGroup F d) =>
      cornerDelete x.val), G ⧸ Γ),
      ∀ x : cosetCornerCubeSet Γ (upperFaceCubeGroup F d),
        R ⟨cornerDelete x.val, ⟨x, rfl⟩⟩ = x.val none := by
  exact compactCorner_continuous_reconstruction _ hcompact
    (upperFaceCubeGroup_coset_corner_unique F hF htop Γ)

theorem upperFaceCubeGroup_boundedLipschitz_recipes (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (Γ : Subgroup G)
    [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (ProperCubeVertex d) (G ⧸ Γ)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A, ∃ r ∈ recipes, ∀ z ∈ upperFaceCubeGroup F d,
        |r.value (cornerDelete (cosetCornerCube Γ z)) - f (z Finset.univ)| < ε) := by
  exact cosetCornerCubeSet_boundedLipschitz_recipes Γ (upperFaceCubeGroup F d)
    (upperFaceCubeGroup_proper_coordinates F hF htop) hcompact A B L hB hL ε hε

end Hindman168
