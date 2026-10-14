import Hindman168.NilUpperFaceOrdering

/-! Actual ordered upper-face factorization of every element in the
filtered face-generated subgroup. Subgroup collection uses the proved
normalization of upward-closed suffixes; no coordinate certificate is
assumed in this construction. -/

namespace Hindman168
open scoped Classical Pointwise

variable {G : Type*} [Group G] {d : ℕ}

theorem upperFaceTailGroup_nil (F : ℕ → Subgroup G) :
    upperFaceTailGroup F ([] : List (Finset (Fin d))) = ⊥ := by
  simp [upperFaceTailGroup]

theorem upperFaceTailGroup_cons (F : ℕ → Subgroup G) (D : Finset (Fin d))
    (faces : List (Finset (Fin d))) :
    upperFaceTailGroup F (D :: faces) = upperFaceSubgroup F D ⊔ upperFaceTailGroup F faces := by
  apply le_antisymm
  · apply (Subgroup.closure_le (K := upperFaceSubgroup F D ⊔ upperFaceTailGroup F faces)).mpr
    intro v hv
    obtain ⟨E, hE, g, hg, rfl⟩ := hv
    rcases List.mem_cons.mp hE with rfl | hE
    · exact Subgroup.mem_sup_left (show upperFaceArray E g ∈ upperFaceSubgroup F E from ⟨g, hg, rfl⟩)
    · exact Subgroup.mem_sup_right (upperFaceTailGroup_generator F faces E hE g hg)
  · apply sup_le
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := hv
      exact upperFaceTailGroup_generator F (D :: faces) D (by simp) g hg
    · apply Subgroup.closure_mono
      rintro v ⟨E, hE, g, hg, rfl⟩
      exact ⟨E, by simp [hE], g, hg, rfl⟩

theorem upperFaceTailGroup_coordinates (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F)
    (faces : List (Finset (Fin d)))
    (horder : faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E))
    (hclosed : UpperFaceTailClosed faces)
    (z : Finset (Fin d) → G) (hz : z ∈ upperFaceTailGroup F faces) :
    ∃ a : Finset (Fin d) → G, (∀ D ∈ faces, a D ∈ F D.card) ∧ z = upperFaceProduct a faces := by
  induction faces generalizing z with
  | nil =>
    have hz1 : z = 1 := by simpa only [upperFaceTailGroup_nil, Subgroup.mem_bot] using hz
    exact ⟨fun _ => 1, by simp, by simpa [upperFaceProduct] using hz1⟩
  | cons D faces ih =>
    have htorder := (List.pairwise_cons.mp horder).2
    have htclosed := upperFaceTailClosed_tail D faces horder hclosed
    have hnorm := upperFaceSubgroup_normalizes_tail F hF D faces htclosed
    rw [upperFaceTailGroup_cons] at hz
    have hmul : z ∈ (upperFaceSubgroup F D : Set (Finset (Fin d) → G)) *
        (upperFaceTailGroup F faces : Set (Finset (Fin d) → G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]
      exact hz
    obtain ⟨v, hv, u, hu, hvu⟩ := hmul
    obtain ⟨g, hg, rfl⟩ := hv
    obtain ⟨a, ha, hcoord⟩ := ih htorder htclosed u hu
    have hD : D ∉ faces := by
      intro h
      exact ((List.pairwise_cons.mp horder).1 D h).2 rfl
    let a' : Finset (Fin d) → G := Function.update a D g
    refine ⟨a', ?_, ?_⟩
    · intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · change Function.update a E g E ∈ F E.card
        rw [Function.update_self]
        exact hg
      · have hED : E ≠ D := by intro h; exact hD (h ▸ hE)
        change Function.update a D g E ∈ F E.card
        rw [Function.update_of_ne hED]
        exact ha E hE
    · calc
        z = upperFaceHom D g * u := hvu.symm
        _ = upperFaceArray D g * upperFaceProduct a faces := by rw [upperFaceHom_apply, hcoord]
        _ = upperFaceProduct a' (D :: faces) := by
          change upperFaceArray D g * upperFaceProduct a faces =
            upperFaceProduct (Function.update a D g) (D :: faces)
          rw [upperFaceProduct_cons, Function.update_self,
            upperFaceProduct_update_outside a D g faces hD]

theorem upperFaceCubeGroup_eq_full_tail (F : ℕ → Subgroup G) :
    upperFaceCubeGroup F d = upperFaceTailGroup F (orderedCubeFaces d) := by
  apply congrArg Subgroup.closure
  ext v
  constructor
  · rintro ⟨D, g, hg, rfl⟩
    exact ⟨D, orderedCubeFaces_mem d D, g, hg, rfl⟩
  · rintro ⟨D, _, g, hg, rfl⟩
    exact ⟨D, g, hg, rfl⟩

theorem upperFaceCubeGroup_coordinates (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F)
    (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d) :
    ∃ a : Finset (Fin d) → G, (∀ D, a D ∈ F D.card) ∧
      ∀ E, z E = upperFaceValue a (orderedCubeFaces d) E := by
  rw [upperFaceCubeGroup_eq_full_tail] at hz
  obtain ⟨a, ha, hcoord⟩ := upperFaceTailGroup_coordinates F hF (orderedCubeFaces d)
    (orderedCubeFaces_pairwise d) (orderedCubeFaces_tailClosed d) z hz
  exact ⟨a, fun D => ha D (orderedCubeFaces_mem d D),
    fun E => by rw [hcoord, upperFaceProduct_apply]⟩

end Hindman168
