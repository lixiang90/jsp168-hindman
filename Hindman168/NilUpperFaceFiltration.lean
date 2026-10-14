import Hindman168.NilUpperFaceGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Exact upper-face homomorphisms, unions of commutator faces, and
the actual filtered face subgroups used in the ordered coordinate proof.
All arguments allow noncommutative groups. -/

namespace Hindman168
open scoped Classical commutatorElement

variable {G : Type*} [Group G] {d : ℕ}

structure CubeGroupFiltration (F : ℕ → Subgroup G) : Prop where
  antitone : Antitone F
  commutator_mem : ∀ i j, ∀ g ∈ F i, ∀ h ∈ F j, ⁅g, h⁆ ∈ F (i+j)

noncomputable def upperFaceHom (D : Finset (Fin d)) : G →* (Finset (Fin d) → G) where
  toFun := upperFaceArray D
  map_one' := by funext E; simp [upperFaceArray]
  map_mul' g h := by funext E; by_cases he : D ⊆ E <;> simp [upperFaceArray, he]

noncomputable def upperFaceSubgroup (F : ℕ → Subgroup G) (D : Finset (Fin d)) :
    Subgroup (Finset (Fin d) → G) := (F D.card).map (upperFaceHom D)

noncomputable def upperFaceTailGroup (F : ℕ → Subgroup G)
    (faces : List (Finset (Fin d))) : Subgroup (Finset (Fin d) → G) :=
  Subgroup.closure {v | ∃ D ∈ faces, ∃ g ∈ F D.card, v = upperFaceArray D g}

theorem upperFaceHom_apply (D : Finset (Fin d)) (g : G) :
    upperFaceHom D g = upperFaceArray D g := rfl

theorem upperFaceArray_commutator (D E : Finset (Fin d)) (g h : G) :
    ⁅upperFaceArray D g, upperFaceArray E h⁆ = upperFaceArray (D ∪ E) ⁅g, h⁆ := by
  funext V
  by_cases hD : D ⊆ V <;> by_cases hE : E ⊆ V <;>
    simp [commutatorElement_def, upperFaceArray, hD, hE, Finset.union_subset_iff]

theorem upperFaceArray_conjugate (D E : Finset (Fin d)) (g h : G) :
    upperFaceArray D g * upperFaceArray E h * (upperFaceArray D g)⁻¹ =
      upperFaceArray (D ∪ E) ⁅g, h⁆ * upperFaceArray E h := by
  rw [← upperFaceArray_commutator]
  simp [commutatorElement_def, mul_assoc]

theorem CubeGroupFiltration.commutator_face_level {F : ℕ → Subgroup G}
    (hF : CubeGroupFiltration F) (D E : Finset (Fin d)) (g h : G)
    (hg : g ∈ F D.card) (hh : h ∈ F E.card) : ⁅g, h⁆ ∈ F (D ∪ E).card := by
  exact hF.antitone (Finset.card_union_le D E) (hF.commutator_mem _ _ g hg h hh)

theorem upperFaceTailGroup_generator (F : ℕ → Subgroup G)
    (faces : List (Finset (Fin d))) (D : Finset (Fin d)) (hD : D ∈ faces)
    (g : G) (hg : g ∈ F D.card) : upperFaceArray D g ∈ upperFaceTailGroup F faces := by
  exact Subgroup.subset_closure ⟨D, hD, g, hg, rfl⟩

def UpperFaceTailClosed (faces : List (Finset (Fin d))) : Prop :=
  ∀ E ∈ faces, ∀ D, E ⊆ D → D ∈ faces

theorem upperFaceSubgroup_normalizes_tail (F : ℕ → Subgroup G) (hF : CubeGroupFiltration F)
    (D : Finset (Fin d)) (faces : List (Finset (Fin d))) (hclosed : UpperFaceTailClosed faces) :
    upperFaceSubgroup F D ≤ Subgroup.normalizer (upperFaceTailGroup F faces : Set (Finset (Fin d) → G)) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro v hv u hu
  obtain ⟨g, hg, rfl⟩ := hv
  obtain ⟨E, hE, h, hh, rfl⟩ := hu
  rw [upperFaceHom_apply, upperFaceArray_conjugate]
  apply (upperFaceTailGroup F faces).mul_mem
  · exact upperFaceTailGroup_generator F faces (D ∪ E)
      (hclosed E hE _ Finset.subset_union_right) ⁅g, h⁆
      (hF.commutator_face_level D E g h hg hh)
  · exact upperFaceTailGroup_generator F faces E hE h hh

end Hindman168
