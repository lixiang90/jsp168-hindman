import Hindman168.RationalLinearLattice
import Mathlib.Algebra.Module.Submodule.Bilinear

/-! Rationality under genuine linear and bilinear span operations. The
hypotheses refer only to the rational structure, not to layer compactness. -/

namespace Hindman168
open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℚ E]

/-- Real spans of rational generators are rational layers. -/
theorem rationalLinearSubspace_of_generators (L : Submodule ℤ E) (s : Set E)
    (hs : s ⊆ span ℚ (L : Set E)) : RationalLinearSubspace L (span ℝ s) := by
  apply le_antisymm
  · exact span_le.mpr fun _ hx => hx.1
  · apply span_le.mpr
    intro x hx
    exact subset_span ⟨subset_span hx, hs hx⟩

/-- The ambient space is rational whenever the integer vectors span it. -/
theorem rationalLinearSubspace_top (L : Submodule ℤ E)
    (hL : span ℝ (L : Set E) = ⊤) : RationalLinearSubspace L ⊤ := by
  have h := rationalLinearSubspace_of_generators L (L : Set E) subset_span
  rwa [hL] at h

/-- A rational-structure-preserving bilinear operation preserves rational
layers, by expanding their rational generators before taking real spans. -/
theorem rationalLinearSubspace_map₂ (L : Submodule ℤ E)
    (f : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hf : ∀ x ∈ span ℚ (L : Set E), ∀ y ∈ span ℚ (L : Set E),
      f x y ∈ span ℚ (L : Set E))
    (V W : Submodule ℝ E) (hV : RationalLinearSubspace L V)
    (hW : RationalLinearSubspace L W) : RationalLinearSubspace L (map₂ f V W) := by
  let s : Set E := (V : Set E) ∩ (span ℚ (L : Set E) : Set E)
  let t : Set E := (W : Set E) ∩ (span ℚ (L : Set E) : Set E)
  have heq : map₂ f V W = span ℝ (Set.image2 (fun x y => f x y) s t) := by
    calc map₂ f V W = map₂ f (span ℝ s) (span ℝ t) :=
           congrArg₂ (map₂ f) hV.symm hW.symm
         _ = span ℝ (Set.image2 (fun x y => f x y) s t) := map₂_span_span ℝ f s t
  rw [heq]
  apply rationalLinearSubspace_of_generators
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact hf x hx.2 y hy.2

/-- Images of rational layers are rational for the image integer structure.
This permits coordinate realizations without conflicting algebraic instances. -/
theorem rationalLinearSubspace_map {F : Type*} [AddCommGroup F]
    [Module ℝ F] [Module ℚ F] (L : Submodule ℤ E) (V : Submodule ℝ E)
    (hV : RationalLinearSubspace L V) (f : E →ₗ[ℝ] F) :
    RationalLinearSubspace (L.map (f.restrictScalars ℤ)) (V.map f) := by
  apply (rationalLinearSubspace_iff_integer_span _ _).mpr
  apply le_antisymm
  · exact span_le.mpr fun _ hx => hx.1
  · have hs := rationalLinearSubspace_integer_span L V hV
    calc V.map f = (span ℝ ((V : Set E) ∩ (L : Set E))).map f :=
           congrArg (fun S : Submodule ℝ E => S.map f) hs.symm
         _ = span ℝ (f '' ((V : Set E) ∩ (L : Set E))) := map_span f _
         _ ≤ span ℝ ((V.map f : Set F) ∩ (L.map (f.restrictScalars ℤ) : Set F)) := ?_
    apply span_mono
    rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩

end Hindman168
