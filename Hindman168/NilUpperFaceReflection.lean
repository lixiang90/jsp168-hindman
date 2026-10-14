import Hindman168.NilUpperFaceMissingCorner
import Mathlib.Data.Finset.BooleanAlgebra

/-! Actual coordinate reflections preserve the filtered upper-face
cube group. A reflected face is either unchanged or the product of
its erased-coordinate face and its original inverse face. -/

namespace Hindman168
open scoped Classical

variable {G : Type*} [Group G] {d : ℕ}

noncomputable def cubeFlip (j : Fin d) (E : Finset (Fin d)) : Finset (Fin d) :=
  if j ∈ E then E.erase j else insert j E

theorem cubeFlip_involutive (j : Fin d) : Function.Involutive (cubeFlip j) := by
  intro E
  by_cases h : j ∈ E
  · simp [cubeFlip, h]
  · simp [cubeFlip, h]

theorem cubeFlip_mem_of_ne (j k : Fin d) (hkj : k ≠ j) (E : Finset (Fin d)) :
    k ∈ cubeFlip j E ↔ k ∈ E := by
  by_cases h : j ∈ E <;> simp [cubeFlip, h, hkj]

noncomputable def cubeFlipHom (j : Fin d) :
    (Finset (Fin d) → G) →* (Finset (Fin d) → G) where
  toFun := fun z E => z (cubeFlip j E)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem cubeFlip_upperFace_not_mem (j : Fin d) (D : Finset (Fin d)) (g : G)
    (hj : j ∉ D) : cubeFlipHom j (upperFaceArray D g) = upperFaceArray D g := by
  funext E
  have heq : D ⊆ cubeFlip j E ↔ D ⊆ E := by
    constructor <;> intro h k hk
    · exact (cubeFlip_mem_of_ne j k (by intro h; exact hj (h ▸ hk)) E).mp (h hk)
    · exact (cubeFlip_mem_of_ne j k (by intro h; exact hj (h ▸ hk)) E).mpr (h hk)
  simp only [cubeFlipHom, MonoidHom.coe_mk, OneHom.coe_mk, upperFaceArray, heq]

theorem cubeFlip_upperFace_mem (j : Fin d) (D : Finset (Fin d)) (g : G)
    (hj : j ∈ D) : cubeFlipHom j (upperFaceArray D g) =
      upperFaceArray (D.erase j) g * upperFaceArray D g⁻¹ := by
  funext E
  have hfull : D ⊆ E ↔ D.erase j ⊆ E ∧ j ∈ E := by
    constructor
    · intro h
      exact ⟨(Finset.erase_subset _ _).trans h, h hj⟩
    · rintro ⟨h, hjE⟩ k hk
      by_cases hkj : k = j
      · exact hkj ▸ hjE
      · exact h (Finset.mem_erase.mpr ⟨hkj, hk⟩)
  have hflip : D ⊆ cubeFlip j E ↔ D.erase j ⊆ E ∧ j ∉ E := by
    by_cases hjE : j ∈ E
    · have hno : ¬ D ⊆ E.erase j := by
        intro h
        exact (Finset.notMem_erase j E) (h hj)
      simp [cubeFlip, hjE, hno]
    · simp [cubeFlip, hjE, Finset.subset_insert_iff]
  change (if D ⊆ cubeFlip j E then g else 1) =
    (if D.erase j ⊆ E then g else 1) * (if D ⊆ E then g⁻¹ else 1)
  simp only [hflip, hfull]
  by_cases hs : D.erase j ⊆ E <;> by_cases hjE : j ∈ E <;> simp [hs, hjE]

theorem upperFaceCubeGroup_flip_mem (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F)
    (j : Fin d) (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d) :
    cubeFlipHom j z ∈ upperFaceCubeGroup F d := by
  have hle : upperFaceCubeGroup F d ≤ (upperFaceCubeGroup F d).comap (cubeFlipHom j) := by
    apply (Subgroup.closure_le (K := (upperFaceCubeGroup F d).comap (cubeFlipHom j))).mpr
    rintro v ⟨D, g, hg, rfl⟩
    change cubeFlipHom j (upperFaceArray D g) ∈ upperFaceCubeGroup F d
    by_cases hj : j ∈ D
    · rw [cubeFlip_upperFace_mem j D g hj]
      exact (upperFaceCubeGroup F d).mul_mem
        (upperFaceArray_mem_cubeGroup F (D.erase j) g
          (hF.antitone (Finset.card_erase_le (s := D) (a := j)) hg))
        (upperFaceArray_mem_cubeGroup F D g⁻¹ ((F D.card).inv_mem hg))
    · rw [cubeFlip_upperFace_not_mem j D g hj]
      exact upperFaceArray_mem_cubeGroup F D g hg
  exact hle hz

noncomputable def cubeReflectList : List (Fin d) → Finset (Fin d) → Finset (Fin d)
  | [], E => E
  | j :: js, E => cubeFlip j (cubeReflectList js E)

theorem upperFaceCubeGroup_reflectList_mem (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F)
    (js : List (Fin d)) (z : Finset (Fin d) → G) (hz : z ∈ upperFaceCubeGroup F d) :
    (fun E => z (cubeReflectList js E)) ∈ upperFaceCubeGroup F d := by
  induction js generalizing z with
  | nil => exact hz
  | cons j js ih =>
    exact ih (cubeFlipHom j z) (upperFaceCubeGroup_flip_mem F hF j z hz)

end Hindman168
