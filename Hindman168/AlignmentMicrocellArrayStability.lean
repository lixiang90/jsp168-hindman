import Hindman168.AlignmentProgressionMicrocellBounds
import Hindman168.AlignmentArrayIntervalStability

/-! Uniform interval stability for the literal array on a whole microcell,
with the original earlier-variable cutoff and exact displacement data. -/

namespace Hindman168

open Filter
open scoped Topology Classical

theorem alignment_progression_microcell_uniform_margin
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ u ∈ U, ∀ t : Fin n → ℕ,
      (∀ j, j < i → t j ≤ F.cutoff w j.val ^ 2) →
      ∀ ρ : AlignmentAddingPair n i → ℕ, (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) →
      ∀ Δ : AlignmentAddingPair n i → ℤ,
      (∀ e, (F.modulus w : ℤ) * Δ e = (alignmentIntegerNumerator q₀ w e t : ℤ) -
        (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ e) →
      ∀ T : Finset (Fin n), |(F.modulus w : ℤ) * alignmentIntegerArrayProgression Δ T u| ≤
        (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ) := by
  filter_upwards [alignment_progression_microcell_uniform_small hF i q₀ U
    (by norm_num : (0 : ℝ) < 1)] with w hw
  intro u hu t ht ρ hρ Δ hexact T
  have hh := hw u hu t ht ρ hρ Δ hexact T
  rw [one_mul] at hh
  exact_mod_cast hh

theorem alignment_microcell_array_uniform_interval_stable
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ v ∈ V, ∀ u ∈ U, ∀ t : Fin n → ℕ,
      (∀ j, j < i → t j ≤ F.cutoff w j.val ^ 2) →
      ∀ ρ : AlignmentAddingPair n i → ℕ, (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) →
      ∀ Δ : AlignmentAddingPair n i → ℤ,
      (∀ e, (F.modulus w : ℤ) * Δ e = (alignmentIntegerNumerator q₀ w e t : ℤ) -
        (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ e) →
      ∀ T : Finset (Fin n), (∀ j ∈ T, j < i) → ∀ p p0 : ℤ,
      |p - p0| ≤ (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ) →
      intervalInteriorRoot (F.gap w i.val)
        (3 * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        ((alignmentNaturalBlockProduct t T : ℤ) * p0) →
      alignmentIntegerArrayArgument t (F.modulus w) ρ Δ T p v u / (F.gap w i.val : ℤ) =
        ((alignmentNaturalBlockProduct t T : ℤ) * p0) / (F.gap w i.val : ℤ) := by
  filter_upwards [alignment_slot_microcell_uniform_margin hF i V,
    alignment_progression_microcell_uniform_margin hF i q₀ U] with w hv hu
  intro v hvV u huU t ht ρ hρ Δ hexact T hT p p0 hp hy
  let R := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
  have hb := alignment_earlier_block_product_bound hF w i t ht T hT
  have ha := F.auxiliary_ge_two w i.val
  have hmargin : alignmentNaturalBlockProduct t T * (R + R) + R ≤
      3 * F.auxiliary w i.val * R := by nlinarith
  have hinterior : intervalInteriorRoot (F.gap w i.val)
      (alignmentNaturalBlockProduct t T * (R + R) + R)
      ((alignmentNaturalBlockProduct t T : ℤ) * p0) := by
    have hm : ((alignmentNaturalBlockProduct t T * (R + R) + R : ℕ) : ℤ) ≤
        (3 * F.auxiliary w i.val * R : ℕ) := by exact_mod_cast hmargin
    exact ⟨hm.trans hy.1, lt_of_le_of_lt (add_le_add le_rfl hm) hy.2⟩
  exact alignmentIntegerArrayArgument_interval_stable t (F.modulus w) ρ Δ T p p0 v u
    (F.gap w i.val) R R R (hF.gap_positive w i.val) hp (hv v hvV ρ hρ)
    (hu u huU t ht ρ hρ Δ hexact T) hinterior

end Hindman168
