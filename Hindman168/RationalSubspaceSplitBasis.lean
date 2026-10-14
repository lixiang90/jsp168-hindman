import Hindman168.RationalSubspaceArbitraryBasis
import Mathlib.LinearAlgebra.Basis.Prod

namespace Hindman168
open Module
open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  (W : Submodule ℚ E) [FiniteDimensional ℚ W]

noncomputable def rationalSubspaceSplitBasis (P Q : Submodule ℚ W) (hPQ : IsCompl P Q) :
    Basis (Fin (Module.finrank ℚ P) ⊕ Fin (Module.finrank ℚ Q)) ℚ W :=
  ((Module.finBasis ℚ P).prod (Module.finBasis ℚ Q)).map (P.prodEquivOfIsCompl Q hPQ)

omit [NormedSpace ℝ E] in
theorem rational_subspace_split_basis_inl (P Q : Submodule ℚ W) (hPQ : IsCompl P Q)
    (i : Fin (Module.finrank ℚ P)) :
    rationalSubspaceSplitBasis W P Q hPQ (Sum.inl i) = (Module.finBasis ℚ P i : W) := by
  simp [rationalSubspaceSplitBasis, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

omit [NormedSpace ℝ E] in
theorem rational_subspace_split_basis_inr (P Q : Submodule ℚ W) (hPQ : IsCompl P Q)
    (i : Fin (Module.finrank ℚ Q)) :
    rationalSubspaceSplitBasis W P Q hPQ (Sum.inr i) = (Module.finBasis ℚ Q i : W) := by
  simp [rationalSubspaceSplitBasis, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

noncomputable def rationalSubspaceRealSplitBasis
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (W : Set E) = ⊤)
    (P Q : Submodule ℚ W) (hPQ : IsCompl P Q) :
    Basis (Fin (Module.finrank ℚ P) ⊕ Fin (Module.finrank ℚ Q)) ℝ E :=
  rationalSubspaceRealBasisOfBasis W hdim hspan (rationalSubspaceSplitBasis W P Q hPQ)

theorem rational_subspace_real_split_basis_rational
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (W : Set E) = ⊤)
    (P Q : Submodule ℚ W) (hPQ : IsCompl P Q)
    (i : Fin (Module.finrank ℚ P) ⊕ Fin (Module.finrank ℚ Q)) :
    rationalSubspaceRealSplitBasis W hdim hspan P Q hPQ i ∈ W := by
  rw [rationalSubspaceRealSplitBasis, rational_subspace_real_basis_of_basis_apply]
  exact (rationalSubspaceSplitBasis W P Q hPQ i).property

theorem rational_subspace_real_split_basis_inl_mem
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (W : Set E) = ⊤) (L : Submodule ℝ E)
    (Q : Submodule ℚ W)
    (hPQ : IsCompl ((L.restrictScalars ℚ).comap W.subtype) Q)
    (i : Fin (Module.finrank ℚ ((L.restrictScalars ℚ).comap W.subtype))) :
    rationalSubspaceRealSplitBasis W hdim hspan
      ((L.restrictScalars ℚ).comap W.subtype) Q hPQ (Sum.inl i) ∈ L := by
  rw [rationalSubspaceRealSplitBasis, rational_subspace_real_basis_of_basis_apply,
    rational_subspace_split_basis_inl]
  exact (Module.finBasis ℚ ((L.restrictScalars ℚ).comap W.subtype) i).property

theorem rational_subspace_real_split_basis_inl_span
    (hdim : Module.finrank ℚ W = Module.finrank ℝ E)
    (hspan : Submodule.span ℝ (W : Set E) = ⊤) (L : Submodule ℝ E)
    (hL : Submodule.span ℝ ((L.restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = L)
    (Q : Submodule ℚ W)
    (hPQ : IsCompl ((L.restrictScalars ℚ).comap W.subtype) Q) :
    Submodule.span ℝ (Set.range (fun i =>
      rationalSubspaceRealSplitBasis W hdim hspan
        ((L.restrictScalars ℚ).comap W.subtype) Q hPQ (Sum.inl i))) = L := by
  let P := (L.restrictScalars ℚ).comap W.subtype
  let a := Module.finBasis ℚ P
  have hP : Submodule.span ℚ (Set.range (fun i => (a i : W))) = P := by
    have he : P.subtype '' Set.range a = Set.range (fun i => (a i : W)) :=
      (Set.range_comp _ _).symm
    rw [← he, ← Submodule.map_span, a.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hm : P.map W.subtype = L.restrictScalars ℚ ⊓ W := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hl, hw⟩
      exact ⟨⟨x, hw⟩, hl, rfl⟩
  have hR : Submodule.span ℚ (Set.range (fun i => ((a i : W) : E))) =
      L.restrictScalars ℚ ⊓ W := by
    have he : W.subtype '' Set.range (fun i => (a i : W)) =
        Set.range (fun i => ((a i : W) : E)) := (Set.range_comp _ _).symm
    rw [← he, ← Submodule.map_span, hP, hm]
  simp only [rationalSubspaceRealSplitBasis, rational_subspace_real_basis_of_basis_apply,
    rational_subspace_split_basis_inl]
  change Submodule.span ℝ (Set.range (fun i => ((a i : W) : E))) = L
  rw [← Submodule.span_span_of_tower (R := ℚ) (S := ℝ), hR]
  exact hL

end Hindman168
