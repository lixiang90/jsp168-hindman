import Hindman168.NativeProjectionCorrelation
import Hindman168.FiniteMassUltrafilterHilbert

/-! Coarse projection approximation controls testing against an actual
native unit-bounded family in the original weighted Hilbert space. -/

namespace Hindman168
open FiniteMass Filter
open scoped Topology
universe u

variable (s : ℕ) {N : ℕ} (F : MasterParameterFamily)
  (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ y, 0 ≤ μ w y)] (U : Ultrafilter ℕ)
  (gap : ℕ → Fin N)

theorem nativeCoarseProjection_inner_testing
    (hprob : ∀ w, total (μ w) ≤ 1)
    (f model v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hv : NativePieceRepresented.{u} s F gap (fun w y => v.val w y))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1)
    (τ : ℝ)
    (happrox : ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection
      (hilbertFamilyToCompletion _ U f) - hilbertFamilyToCompletion _ U model‖ < τ) :
    |inner ℝ (hilbertFamilyToCompletion _ U (f-model))
      (hilbertFamilyToCompletion _ U v)| < τ := by
  have hv' := nativeHilbertRepresentation_mem_closed s F μ U gap ⟨v, hv, rfl⟩
  have hn : ‖hilbertFamilyToCompletion _ U v‖ ≤ 1 := by
    apply hilbertFamilyToCompletion_norm_le _ U v zero_le_one
    exact fun w => finiteMassL2_norm_le_subprob (μ w) (hprob w) (v.val w) zero_le_one (hb w)
  have he := (nativeNilHilbertSubspace.{u} s F μ U gap).starProjection_inner_eq_zero
    (hilbertFamilyToCompletion _ U f) (hilbertFamilyToCompletion _ U v) hv'
  rw [inner_sub_left, sub_eq_zero] at he
  have hm : hilbertFamilyToCompletion _ U (f-model) =
      hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U model :=
    map_sub (hilbertFamilyCompletionLinearMap _ U) f model
  rw [hm, inner_sub_left, he, ← inner_sub_left]
  exact ((abs_real_inner_le_norm _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg _))).trans_lt happrox

theorem nativeCoarseProjection_expectation_testing
    (hprob : ∀ w, total (μ w) ≤ 1)
    (f model v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hv : NativePieceRepresented.{u} s F gap (fun w y => v.val w y))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1)
    (τ : ℝ)
    (happrox : ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection
      (hilbertFamilyToCompletion _ U f) - hilbertFamilyToCompletion _ U model‖ < τ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in (U : Filter ℕ),
      |expectation (μ w) (fun y => (f.val w y - model.val w y) * v.val w y)| < τ + η := by
  have hc := nativeCoarseProjection_inner_testing s F μ U gap hprob f model v hv hb τ happrox
  have ht := (finiteMassHilbert_expectation_tendsto μ U (f-model) v).abs
  have h := ht.eventually (Iio_mem_nhds (hc.trans (lt_add_of_pos_right τ hη)))
  change ∀ᶠ w in (U : Filter ℕ),
    |expectation (μ w) (fun y => (f.val w y - model.val w y) * v.val w y)| < τ + η at h
  exact h

end Hindman168
