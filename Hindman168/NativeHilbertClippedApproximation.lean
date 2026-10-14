import Hindman168.NativeHilbertRepresentations
import Hindman168.FiniteMassHilbertClipping

/-! Dense approximation of the actual coarse projection by a single
native representation, clipped pointwise to [0,1]. -/

namespace Hindman168
open FiniteMass Filter
universe u

variable (s : ℕ) {N : ℕ} (F : MasterParameterFamily)
  (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ a, 0 ≤ μ w a)] (U : Ultrafilter ℕ)
  (gap : ℕ → Fin N)

theorem nativeHilbertRepresentation_mem_closed
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (μ w)) U}
    (hz : z ∈ nativeHilbertRepresentations.{u} s F μ U gap) :
    z ∈ nativeNilHilbertSubspace.{u} s F μ U gap :=
  Submodule.le_topologicalClosure _ hz

theorem nativeHilbertRepresentation_clip (hprob : ∀ w, total (μ w) = 1)
    (t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (ht : NativePieceRepresented.{u} s F gap (fun w y => t.val w y)) :
    hilbertFamilyToCompletion _ U (finiteMassClipFamily μ hprob t) ∈
      nativeHilbertRepresentations.{u} s F μ U gap := by
  obtain ⟨D, hD⟩ := ht
  exact ⟨finiteMassClipFamily μ hprob t, ⟨D, nativePieceOn_clip D F gap _ hD⟩, rfl⟩

theorem nativeHilbert_projection_clip_distance_le (hprob : ∀ w, total (μ w) = 1)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w y, y ∈ (μ w).support → 0 ≤ f.val w y ∧ f.val w y ≤ 1)
    (ht : NativePieceRepresented.{u} s F gap (fun w y => t.val w y)) :
    ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection (hilbertFamilyToCompletion _ U f) -
      hilbertFamilyToCompletion _ U (finiteMassClipFamily μ hprob t)‖ ≤
    ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection (hilbertFamilyToCompletion _ U f) -
      hilbertFamilyToCompletion _ U t‖ := by
  apply projection_clipping_distance_le
  · exact nativeHilbertRepresentation_mem_closed s F μ U gap ⟨t, ht, rfl⟩
  · exact nativeHilbertRepresentation_mem_closed s F μ U gap
      (nativeHilbertRepresentation_clip s F μ U gap hprob t ht)
  · exact finiteMassHilbert_clip_distance_le μ U hprob f t hf

theorem nativeHilbert_clipped_approximation (hprob : ∀ w, total (μ w) = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w y, y ∈ (μ w).support → 0 ≤ f.val w y ∧ f.val w y ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)),
      NativePieceRepresented.{u} s F gap (fun w y => t.val w y) ∧
      (∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1) ∧
      ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection (hilbertFamilyToCompletion _ U f) -
        hilbertFamilyToCompletion _ U t‖ < ε := by
  let V := nativeNilHilbertSubspace.{u} s F μ U gap
  have hp : V.starProjection (hilbertFamilyToCompletion _ U f) ∈
      closure (nativeHilbertRepresentations.{u} s F μ U gap : Set _) :=
    V.starProjection_apply_mem _
  obtain ⟨z, hz, he⟩ := Metric.mem_closure_iff.mp hp ε hε
  obtain ⟨t, ht, rfl⟩ := (mem_nativeHilbertRepresentations_iff s F μ U gap z).mp hz
  refine ⟨finiteMassClipFamily μ hprob t, ?_, ?_, ?_⟩
  · obtain ⟨D, hD⟩ := ht
    exact ⟨D, nativePieceOn_clip D F gap _ hD⟩
  · exact fun w y => unitIntervalClip_bounds _
  · exact (nativeHilbert_projection_clip_distance_le s F μ U gap hprob f t hf ht).trans_lt
      (by simpa only [dist_eq_norm] using he)

theorem nativeHilbert_clipped_fine_error (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val)
    (hprob : ∀ w, total (μ w) = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w y, y ∈ (μ w).support → 0 ≤ f.val w y ∧ f.val w y ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (henergy : ‖(nativeNilHilbertSubspace.{u} s F μ U fine).starProjection
        (hilbertFamilyToCompletion _ U f)‖ ^ 2 -
      ‖(nativeNilHilbertSubspace.{u} s F μ U coarse).starProjection
        (hilbertFamilyToCompletion _ U f)‖ ^ 2 ≤ ε ^ 2) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)),
      NativePieceRepresented.{u} s F coarse (fun w y => t.val w y) ∧
      (∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1) ∧
      ‖(nativeNilHilbertSubspace.{u} s F μ U coarse).starProjection (hilbertFamilyToCompletion _ U f) -
        hilbertFamilyToCompletion _ U t‖ < ε ∧
      ‖(nativeNilHilbertSubspace.{u} s F μ U fine).starProjection
        (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t)‖ ≤ 2 * ε := by
  obtain ⟨t, ht, hb, he⟩ := nativeHilbert_clipped_approximation s F μ U coarse hprob f hf hε
  refine ⟨t, ht, hb, he, ?_⟩
  exact nested_projection_model_error _ _
    (nativeNilHilbertSubspace_refine s F μ U fine coarse hdiv) _ _
    (nativeHilbertRepresentation_mem_closed s F μ U coarse ⟨t, ht, rfl⟩)
    hε.le henergy he.le

end Hindman168
