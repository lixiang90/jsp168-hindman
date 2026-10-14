import Hindman168.NilUpperFaceCoordinates

/-! Reverse inclusion in the upper-face generated group, by eliminating
actual vertices. The triangular layer condition will be discharged from
native logarithms, not assumed for the final native cube theorem. -/
namespace Hindman168
open scoped Classical
variable {G : Type*} [Group G] {d : ℕ}

theorem upper_face_group_vertex_elimination (F : ℕ → Subgroup G)
    (B : Subgroup (Finset (Fin d) → G))
    (hface : ∀ D g, g ∈ F D.card → upperFaceArray D g ∈ B)
    (hlayer : ∀ z ∈ B, ∀ D, (∀ E, E ⊂ D → z E = 1) → z D ∈ F D.card)
    (faces : List (Finset (Fin d)))
    (horder : faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E))
    (hclosed : UpperFaceTailClosed faces)
    (z : Finset (Fin d) → G) (hz : z ∈ B) (hout : ∀ V, V ∉ faces → z V = 1) :
    z ∈ upperFaceCubeGroup F d := by
  induction faces generalizing z with
  | nil =>
    have he : z = 1 := funext (fun V => hout V (by simp))
    rw [he]
    exact Subgroup.one_mem _
  | cons D faces ih =>
    have hD : z D ∈ F D.card := by
      apply hlayer z hz D
      intro E hE
      apply hout
      intro hmem
      rcases List.mem_cons.mp hmem with he | he
      · subst E; exact (Finset.ssubset_iff_subset_ne.mp hE).2 rfl
      · have hc := ((List.pairwise_cons.mp horder).1 E he).1
        exact (not_lt_of_ge hc) (Finset.card_lt_card hE)
    let a := upperFaceArray D (z D)
    let w := a⁻¹ * z
    have hw : w ∈ B := B.mul_mem (B.inv_mem (hface D (z D) hD)) hz
    have hwout : ∀ V, V ∉ faces → w V = 1 := by
      intro V hV
      by_cases he : V=D
      · subst V; simp [w,a,upperFaceArray]
      · have hnot : V ∉ D::faces := by simp [he,hV]
        have hsub : ¬D ⊆ V := by
          intro hDV
          exact hnot (hclosed D (by simp) V hDV)
        simp [w,a,upperFaceArray,hsub,hout V hnot]
    have hm := ih (List.pairwise_cons.mp horder).2
      (upperFaceTailClosed_tail D faces horder hclosed) w hw hwout
    have he : z = a*w := by dsimp [w]; simp
    rw [he]
    exact (upperFaceCubeGroup F d).mul_mem (upperFaceArray_mem_cubeGroup F D (z D) hD) hm

theorem upper_face_group_eq_of_vertex_layers (F : ℕ → Subgroup G)
    (B : Subgroup (Finset (Fin d) → G))
    (hface : ∀ D g, g ∈ F D.card → upperFaceArray D g ∈ B)
    (hlayer : ∀ z ∈ B, ∀ D, (∀ E, E ⊂ D → z E = 1) → z D ∈ F D.card) :
    B = upperFaceCubeGroup F d := by
  apply le_antisymm
  · intro z hz
    exact upper_face_group_vertex_elimination F B hface hlayer (orderedCubeFaces d)
      (orderedCubeFaces_pairwise d) (orderedCubeFaces_tailClosed d) z hz
      (fun V hV => False.elim (hV (orderedCubeFaces_mem d V)))
  · apply (Subgroup.closure_le (K := B)).mpr
    rintro _ ⟨D,g,hg,rfl⟩
    exact hface D g hg

end Hindman168
