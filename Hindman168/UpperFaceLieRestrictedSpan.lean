import Hindman168.UpperFaceLieFiltration

/-! Layerwise rational spanning passes to the actual cube arrays.
The result does not yet identify the lattice in a native product group. -/
namespace Hindman168
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem upper_face_lie_layer_restricted_span (F : ℕ → Submodule R L)
    (P : L → Prop) (hzero : P 0)
    (hspan : ∀ i, Submodule.span R {x | x ∈ F i ∧ P x} = F i) (d i : ℕ) :
    Submodule.span R {z | z ∈ upperFaceLieLayer F d i ∧ ∀ V, P (z V)} =
      upperFaceLieLayer F d i := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hz => hz.1)
  · apply Submodule.span_le.mpr
    rintro _ ⟨D,x,hx,rfl⟩
    have hx' : x ∈ Submodule.span R {x | x ∈ F (max i D.card) ∧ P x} := by
      rw [hspan]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      apply Submodule.subset_span
      refine ⟨upper_face_lie_layer_generator F d i D y hy.1,?_⟩
      intro V
      change P (if D ⊆ V then y else 0)
      split_ifs
      · exact hy.2
      · exact hzero
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end Hindman168
