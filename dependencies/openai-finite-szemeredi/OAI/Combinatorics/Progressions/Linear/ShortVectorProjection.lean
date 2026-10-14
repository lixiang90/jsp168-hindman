/-
Copyright OpenAI contributors. Licensed under Apache-2.0; see dependencies/openai-finite-szemeredi/LICENSE.
Original source: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Modified for Lean 4.32.2 / mathlib 905b958 compatibility.
Original hashes and exact compatibility changes:
dependencies/openai-finite-szemeredi/NATIVE-INVERSE-SOURCE-MANIFEST.json.
-/
import OAI.Combinatorics.Progressions.Lattices.DenseIntegerSpan
import OAI.Combinatorics.Progressions.Lattices.LatticeVoronoiPacking

namespace OAI

section

namespace Erdos3

theorem shortVectorSpan_map_eq_top_of_spanning_integer_images
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) (H : Finset (ι → ℤ)) (R : ℝ)
    (hspan : Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤)
    (hlift : ∀ h ∈ H, ∃ v ∈ Λ, ‖v‖ ≤ R ∧ π v = fun i => (h i : ℝ)) :
    (shortVectorSpan Λ R).map π = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨h, hh, rfl⟩
  obtain ⟨v, hv, hnorm, hπ⟩ := hlift h hh
  exact ⟨v, mem_shortVectorSpan Λ R hv hnorm, hπ⟩

theorem shortVectorSpan_map_eq_top_of_dense_integer_images
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R δ : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card ι - 1) < δ * T i)
    (hlift : ∀ h ∈ H, ∃ v ∈ Λ, ‖v‖ ≤ R ∧ π v = fun i => (h i : ℝ)) :
    (shortVectorSpan Λ R).map π = ⊤ := by
  have hspan := integer_points_span_eq_top_of_density H T R δ hT hR hbound hdense hlarge
  exact shortVectorSpan_map_eq_top_of_spanning_integer_images Λ π H R hspan hlift

end Erdos3

end

end OAI
