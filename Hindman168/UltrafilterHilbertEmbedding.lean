import Hindman168.UltrafilterHilbertCompletion
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.Linarith

/-! Linear realization, zero-distance identification and ordinary-limit
compatibility for the completed ultrafilter Hilbert space. -/

namespace Hindman168
open Filter UniformSpace
open scoped Topology

variable (E : ℕ → Type*) [∀ w, SeminormedAddCommGroup (E w)]
  [∀ w, InnerProductSpace ℝ (E w)] (U : Ultrafilter ℕ)

noncomputable def hilbertFamilyCompletionLinearMap :
    boundedHilbertFamilies E →ₗ[ℝ] UltrafilterHilbertSpace E U where
  toFun := hilbertFamilyToCompletion E U
  map_add' x y := Completion.coe_add (show UltrafilterFamily E U from x) y
  map_smul' r x := Completion.coe_smul r (show UltrafilterFamily E U from x)

theorem hilbertFamilyToCompletion_norm_sq (x : boundedHilbertFamilies E) :
    ‖hilbertFamilyToCompletion E U x‖ ^ 2 = hilbertFamilyPairing E U x x := by
  rw [← real_inner_self_eq_norm_sq, hilbertFamilyToCompletion_inner]

theorem hilbertFamilyToCompletion_norm_sub_sq_tendsto (x y : boundedHilbertFamilies E) :
    Tendsto (fun w => ‖x.val w - y.val w‖ ^ 2) (U : Filter ℕ)
      (𝓝 (‖hilbertFamilyToCompletion E U x - hilbertFamilyToCompletion E U y‖ ^ 2)) := by
  have hm : hilbertFamilyToCompletion E U (x - y) =
      hilbertFamilyToCompletion E U x - hilbertFamilyToCompletion E U y :=
    map_sub (hilbertFamilyCompletionLinearMap E U) x y
  rw [← hm, hilbertFamilyToCompletion_norm_sq]
  simpa only [Submodule.coe_sub, Pi.sub_apply, real_inner_self_eq_norm_sq] using
    hilbertFamilyPairing_tendsto E U (x - y) (x - y)

theorem hilbertFamilyToCompletion_eq_iff (x y : boundedHilbertFamilies E) :
    hilbertFamilyToCompletion E U x = hilbertFamilyToCompletion E U y ↔
      Tendsto (fun w => ‖x.val w - y.val w‖ ^ 2) (U : Filter ℕ) (𝓝 0) := by
  constructor
  · intro h
    simpa only [h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      hilbertFamilyToCompletion_norm_sub_sq_tendsto E U x y
  · intro h
    have hz := tendsto_nhds_unique (hilbertFamilyToCompletion_norm_sub_sq_tendsto E U x y) h
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem hilbertFamilyToCompletion_norm_le (x : boundedHilbertFamilies E) {B : ℝ}
    (hB : 0 ≤ B) (hx : ∀ w, ‖x.val w‖ ≤ B) : ‖hilbertFamilyToCompletion E U x‖ ≤ B := by
  have ht : Tendsto (fun w => ‖x.val w‖ ^ 2) (U : Filter ℕ)
      (𝓝 (‖hilbertFamilyToCompletion E U x‖ ^ 2)) := by
    rw [hilbertFamilyToCompletion_norm_sq]
    simpa only [real_inner_self_eq_norm_sq] using hilbertFamilyPairing_tendsto E U x x
  have hsq := le_of_tendsto ht (Eventually.of_forall (fun w =>
    (sq_le_sq₀ (norm_nonneg _) hB).mpr (hx w)))
  nlinarith [norm_nonneg (hilbertFamilyToCompletion E U x)]

omit U in
theorem hilbertFamilyPairing_hyperfilter_of_tendsto (x y : boundedHilbertFamilies E) (a : ℝ)
    (h : Tendsto (fun w => inner ℝ (x.val w) (y.val w)) atTop (𝓝 a)) :
    hilbertFamilyPairing E (Filter.hyperfilter ℕ) x y = a :=
  tendsto_nhds_unique (hilbertFamilyPairing_tendsto E (Filter.hyperfilter ℕ) x y)
    (h.mono_left Nat.hyperfilter_le_atTop)

end Hindman168
