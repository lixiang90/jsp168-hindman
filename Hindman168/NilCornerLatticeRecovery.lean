import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise

/-! The algebraic lattice-recovery step in the paper's upper-face proof
of missing-corner uniqueness. The lattice is an arbitrary subgroup; no
normality or commutativity assumption is used. Existence of upper-face
coordinates for the filtered nilpotent cube group remains a separate
Lie/group-theoretic obligation. -/

namespace Hindman168
open scoped Classical

variable {I G : Type*} [Group G]

noncomputable def triangularFaceValue (R : I → I → Prop) (a : I → G)
    (faces : List I) (vertex : I) : G :=
  (faces.map (fun D => if R D vertex then a D else 1)).prod

theorem triangularFaceValue_cons (R : I → I → Prop) (a : I → G)
    (D : I) (faces : List I) (vertex : I) :
    triangularFaceValue R a (D :: faces) vertex =
      (if R D vertex then a D else 1) * triangularFaceValue R a faces vertex := by
  simp [triangularFaceValue]

theorem triangularFaceValue_eq_one (R : I → I → Prop) (a : I → G)
    (faces : List I) (vertex : I) (h : ∀ D ∈ faces, ¬ R D vertex) :
    triangularFaceValue R a faces vertex = 1 := by
  induction faces with
  | nil => rfl
  | cons D faces ih =>
    rw [triangularFaceValue_cons, if_neg (h D (by simp)),
      ih (fun E hE => h E (by simp [hE])), one_mul]

theorem triangularFaceValue_lattice_recovery (Γ : Subgroup G) (R : I → I → Prop)
    (hR : ∀ D, R D D) (a : I → G) (faces : List I)
    (horder : faces.Pairwise (fun D E => ¬ R E D))
    (hvertices : ∀ D ∈ faces, triangularFaceValue R a faces D ∈ Γ) :
    ∀ D ∈ faces, a D ∈ Γ := by
  induction faces with
  | nil => simp
  | cons D faces ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    have hD : a D ∈ Γ := by
      have hv := hvertices D (by simp)
      rwa [triangularFaceValue_cons, if_pos (hR D),
        triangularFaceValue_eq_one R a faces D hhead, mul_one] at hv
    have hrest : ∀ E ∈ faces, triangularFaceValue R a faces E ∈ Γ := by
      intro E hE
      have hp : (if R D E then a D else 1) ∈ Γ := by
        split_ifs
        · exact hD
        · exact Γ.one_mem
      have hv := hvertices E (by simp [hE])
      rw [triangularFaceValue_cons] at hv
      simpa only [inv_mul_cancel_left] using Γ.mul_mem (Γ.inv_mem hp) hv
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hD
    · exact ih htail hrest E hE

noncomputable def upperFaceValue {d : ℕ} (a : Finset (Fin d) → G)
    (faces : List (Finset (Fin d))) (vertex : Finset (Fin d)) : G :=
  triangularFaceValue (fun D E => D ⊆ E) a faces vertex

theorem upperFaceValue_lattice_recovery {d : ℕ} (Γ : Subgroup G)
    (a : Finset (Fin d) → G) (faces : List (Finset (Fin d)))
    (horder : faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E))
    (hvertices : ∀ D ∈ faces, upperFaceValue a faces D ∈ Γ) :
    ∀ D ∈ faces, a D ∈ Γ := by
  apply triangularFaceValue_lattice_recovery Γ (fun D E => D ⊆ E)
    (fun D => Finset.Subset.refl D) a faces
  · exact horder.imp (fun {D E} h hED => h.2 (Finset.eq_of_subset_of_card_le hED h.1).symm)
  · exact hvertices

theorem upperFaceValue_mem_lattice {d : ℕ} (Γ : Subgroup G)
    (a : Finset (Fin d) → G) (faces : List (Finset (Fin d)))
    (ha : ∀ D ∈ faces, a D ∈ Γ) (vertex : Finset (Fin d)) :
    upperFaceValue a faces vertex ∈ Γ := by
  apply Γ.list_prod_mem
  intro g hg
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hg
  split_ifs
  · exact ha D hD
  · exact Γ.one_mem

theorem upperFace_coset_missing_top {d : ℕ} (Γ : Subgroup G)
    (x y : Finset (Fin d) → G) (a : Finset (Fin d) → G)
    (faces : List (Finset (Fin d)))
    (hproper : ∀ D ∈ faces, D ≠ Finset.univ)
    (horder : faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E))
    (hcoordinates : ∀ E, (x E)⁻¹ * y E = upperFaceValue a faces E)
    (hpartial : ∀ E ≠ Finset.univ, (x E : G ⧸ Γ) = (y E : G ⧸ Γ)) :
    (x Finset.univ : G ⧸ Γ) = (y Finset.univ : G ⧸ Γ) := by
  have hv : ∀ D ∈ faces, upperFaceValue a faces D ∈ Γ := by
    intro D hD
    rw [← hcoordinates]
    exact QuotientGroup.eq.mp (hpartial D (hproper D hD))
  have ha := upperFaceValue_lattice_recovery Γ a faces horder hv
  apply QuotientGroup.eq.mpr
  rw [hcoordinates]
  exact upperFaceValue_mem_lattice Γ a faces ha _

end Hindman168
