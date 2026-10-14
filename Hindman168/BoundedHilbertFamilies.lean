import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Ultrafilter

/-! Uniformly norm-bounded families in varying real inner product spaces,
and genuine ultrafilter limits of their scalar pairings. -/

namespace Hindman168
open Filter
open scoped Topology

variable (E : ℕ → Type*) [∀ w, SeminormedAddCommGroup (E w)]
  [∀ w, InnerProductSpace ℝ (E w)]

def boundedHilbertFamilies : Submodule ℝ (∀ w, E w) where
  carrier := {x | ∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖x w‖ ≤ B}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  add_mem' := by
    rintro x y ⟨B, hB, hx⟩ ⟨C, hC, hy⟩
    exact ⟨B + C, add_nonneg hB hC, fun w =>
      (norm_add_le (x w) (y w)).trans (add_le_add (hx w) (hy w))⟩
  smul_mem' := by
    rintro r x ⟨B, hB, hx⟩
    refine ⟨‖r‖ * B, mul_nonneg (norm_nonneg _) hB, ?_⟩
    intro w
    exact (norm_smul_le r (x w)).trans (mul_le_mul_of_nonneg_left (hx w) (norm_nonneg r))

theorem boundedHilbertFamilies_pairing_bounded (x y : boundedHilbertFamilies E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w, |inner ℝ (x.val w) (y.val w)| ≤ B := by
  obtain ⟨B, hB, hx⟩ := x.property
  obtain ⟨C, hC, hy⟩ := y.property
  refine ⟨B * C, mul_nonneg hB hC, ?_⟩
  intro w
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul (hx w) (hy w) (norm_nonneg _) hB)

omit [∀ w, SeminormedAddCommGroup (E w)] [∀ w, InnerProductSpace ℝ (E w)] in
theorem bounded_real_ultrafilter_tendsto (U : Ultrafilter ℕ) (f : ℕ → ℝ)
    (hf : ∃ B : ℝ, 0 ≤ B ∧ ∀ w, |f w| ≤ B) :
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) := by
  obtain ⟨B, _, hB⟩ := hf
  have hm : (Ultrafilter.map f U : Filter ℝ) ≤ 𝓟 (Set.Icc (-B) B) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff]
    change ∀ᶠ w in (U : Filter ℕ), f w ∈ Set.Icc (-B) B
    exact Filter.Eventually.of_forall (fun w => abs_le.mp (hB w))
  obtain ⟨a, _, ha⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map f U) hm
  exact tendsto_nhds_limUnder ⟨a, ha⟩

noncomputable def hilbertFamilyPairing (U : Ultrafilter ℕ)
    (x y : boundedHilbertFamilies E) : ℝ :=
  limUnder (U : Filter ℕ) (fun w => inner ℝ (x.val w) (y.val w))

theorem hilbertFamilyPairing_tendsto (U : Ultrafilter ℕ) (x y : boundedHilbertFamilies E) :
    Tendsto (fun w => inner ℝ (x.val w) (y.val w)) (U : Filter ℕ)
      (𝓝 (hilbertFamilyPairing E U x y)) :=
  bounded_real_ultrafilter_tendsto U _ (boundedHilbertFamilies_pairing_bounded E x y)

end Hindman168
