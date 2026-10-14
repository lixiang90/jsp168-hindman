import Hindman168.NilUpperFaceCoordinates

/-! Triangular recovery also proves uniqueness of the actually constructed
ordered face coefficients. The full coordinate theorem therefore gives
existence and uniqueness, not only some coordinate representation. -/

namespace Hindman168
open scoped Classical

variable {G : Type*} [Group G] {d : ℕ}

theorem upperFaceProduct_first_value (a : Finset (Fin d) → G)
    (D : Finset (Fin d)) (faces : List (Finset (Fin d)))
    (horder : (D :: faces).Pairwise (fun E V => E.card ≤ V.card ∧ E ≠ V)) :
    upperFaceProduct a (D :: faces) D = a D := by
  rw [upperFaceProduct_apply, upperFaceValue, triangularFaceValue_cons]
  have ht : triangularFaceValue (fun E V => E ⊆ V) a faces D = 1 := by
    apply triangularFaceValue_eq_one
    intro E hE hED
    have hp := (List.pairwise_cons.mp horder).1 E hE
    exact hp.2 (Finset.eq_of_subset_of_card_le hED hp.1).symm
  simp only [Finset.Subset.refl, if_true, ht, mul_one]

theorem upperFaceProduct_coordinates_unique (faces : List (Finset (Fin d)))
    (horder : faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E))
    (a b : Finset (Fin d) → G) (heq : upperFaceProduct a faces = upperFaceProduct b faces) :
    ∀ D ∈ faces, a D = b D := by
  induction faces with
  | nil => simp
  | cons D faces ih =>
    have hD : a D = b D := by
      have hp := congrFun heq D
      simpa only [upperFaceProduct_first_value a D faces horder,
        upperFaceProduct_first_value b D faces horder] using hp
    have hrest : upperFaceProduct a faces = upperFaceProduct b faces := by
      rw [upperFaceProduct_cons, upperFaceProduct_cons, hD] at heq
      exact mul_left_cancel heq
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hD
    · exact ih (List.pairwise_cons.mp horder).2 hrest E hE

theorem upperFaceProduct_full_injective :
    Function.Injective (fun a : Finset (Fin d) → G => upperFaceProduct a (orderedCubeFaces d)) := by
  intro a b hab
  funext D
  exact upperFaceProduct_coordinates_unique _ (orderedCubeFaces_pairwise d) a b hab D
    (orderedCubeFaces_mem d D)

theorem upperFaceCubeGroup_unique_coordinates (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d) :
    ∃! a : Finset (Fin d) → G, (∀ D, a D ∈ F D.card) ∧
      ∀ E, z E = upperFaceValue a (orderedCubeFaces d) E := by
  obtain ⟨a, ha, hcoord⟩ := upperFaceCubeGroup_coordinates F hF z hz
  refine ⟨a, ⟨ha, hcoord⟩, ?_⟩
  rintro b ⟨_, hb⟩
  apply upperFaceProduct_full_injective
  funext E
  change upperFaceProduct b (orderedCubeFaces d) E = upperFaceProduct a (orderedCubeFaces d) E
  rw [upperFaceProduct_apply, upperFaceProduct_apply, ← hb E, ← hcoord E]

end Hindman168
