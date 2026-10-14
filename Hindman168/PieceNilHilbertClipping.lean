import Hindman168.PieceNilHilbertSubspace
import Hindman168.FiniteMassHilbertClipping

/-! The paper's clipping comparison for genuine representing families
inside their actual original-law closed Hilbert span. -/

namespace Hindman168
open FiniteMass Filter

variable {G : Type*} [Group G] (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] {N : ℕ}
  (F : MasterParameterFamily) (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ a, 0 ≤ μ w a)]
  (U : Ultrafilter ℕ) (gap : ℕ → Fin N)

theorem pieceNilHilbertGenerator_mem_subspace
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U}
    (hz : z ∈ pieceNilHilbertGenerators Γ F μ U gap) :
    z ∈ pieceNilHilbertSubspace Γ F μ U gap :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span hz)

theorem pieceNilHilbertGenerator_clip (hprob : ∀ w, total (μ w) = 1)
    (t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (ht : IsBoundedPieceNilsequence Γ F gap (fun w y => t.val w y)) :
    hilbertFamilyToCompletion _ U (finiteMassClipFamily μ hprob t) ∈
      pieceNilHilbertGenerators Γ F μ U gap := by
  refine ⟨finiteMassClipFamily μ hprob t, ?_, rfl⟩
  exact boundedPieceNilsequence_clip Γ F gap _ ht

theorem pieceNilHilbert_projection_clip_distance_le (hprob : ∀ w, total (μ w) = 1)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w y, y ∈ (μ w).support → 0 ≤ f.val w y ∧ f.val w y ≤ 1)
    (ht : IsBoundedPieceNilsequence Γ F gap (fun w y => t.val w y)) :
    ‖(pieceNilHilbertSubspace Γ F μ U gap).starProjection (hilbertFamilyToCompletion _ U f) -
      hilbertFamilyToCompletion _ U (finiteMassClipFamily μ hprob t)‖ ≤
    ‖(pieceNilHilbertSubspace Γ F μ U gap).starProjection (hilbertFamilyToCompletion _ U f) -
      hilbertFamilyToCompletion _ U t‖ := by
  apply projection_clipping_distance_le
  · exact pieceNilHilbertGenerator_mem_subspace Γ F μ U gap ⟨t, ht, rfl⟩
  · exact pieceNilHilbertGenerator_mem_subspace Γ F μ U gap
      (pieceNilHilbertGenerator_clip Γ F μ U gap hprob t ht)
  · exact finiteMassHilbert_clip_distance_le μ U hprob f t hf

end Hindman168
