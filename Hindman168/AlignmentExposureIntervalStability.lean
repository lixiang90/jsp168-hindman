import Hindman168.AlignmentShortExposureDistance
import Hindman168.AlignmentMicrocellArrayStability

namespace Hindman168

open Filter
open scoped Topology Classical

theorem alignment_exposure_uniform_interval_stable
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ C : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ T : Finset (Fin n), (∀ j ∈ T, j < i) → ∀ x y : Fin n → ℕ,
      (∀ j, j < i → x j ≤ F.cutoff w j.val ^ 2) → (∀ j ∈ T, 0 < x j) →
      (∀ j, j < i → y j ≤ F.cutoff w j.val ^ 2) →
      alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y →
      intervalInteriorRoot (F.gap w i.val)
        ((C + 3) * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) →
      ∀ v ∈ V, ∀ u ∈ U, ∀ ρ : AlignmentAddingPair n i → ℕ,
      (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) → ∀ Δ : AlignmentAddingPair n i → ℤ,
      (∀ e, (F.modulus w : ℤ) * Δ e = (alignmentIntegerNumerator q₀ w e y : ℤ) -
        (alignmentNaturalBlockProduct y e.targetTail : ℤ) * ρ e) →
      ∀ p : ℤ, |p - y i| ≤ (C * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) →
      alignmentIntegerArrayArgument y (F.modulus w) ρ Δ T p v u / (F.gap w i.val : ℤ) =
        ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ) := by
  filter_upwards [alignment_slot_microcell_uniform_margin hF i V,
    alignment_progression_microcell_uniform_margin hF i q₀ U,
    master_microcell_eventually_positive hF (fun _ => i)] with w hv hu hR
  intro T hT x y hx hpos hy hkey hinterior v hvV u huU ρ hρ Δ hΔ p hp
  let R := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
  let L := F.auxiliary w i.val
  have hdist := alignmentShortExposureKey_product_distance hF w i T hT hx hpos hR hkey
  have htail : (alignmentNaturalBlockProduct y T : ℤ) ≤ L := by
    exact_mod_cast alignment_earlier_block_product_bound hF w i y hy T hT
  have hL : (2 : ℤ) ≤ L := by exact_mod_cast F.auxiliary_ge_two w i.val
  have hslot := hv v hvV ρ hρ
  have hprog := hu u huU y hy ρ hρ Δ hΔ T
  have hlocal : |alignmentIntegerArrayArgument y (F.modulus w) ρ Δ T p v u -
      (alignmentNaturalBlockProduct y T : ℤ) * y i| ≤ ((C + 2) * L * R : ℕ) := by
    rw [alignmentIntegerArrayArgument_difference]
    have ha := (abs_add_le (p - (y i : ℤ)) (alignmentIntegerSlotShift ρ v)).trans (add_le_add hp hslot)
    have hb := mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg (alignmentNaturalBlockProduct y T))
    have hc := abs_add_le
      ((alignmentNaturalBlockProduct y T : ℤ) * (p - y i + alignmentIntegerSlotShift ρ v))
      ((F.modulus w : ℤ) * alignmentIntegerArrayProgression Δ T u)
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)] at hc
    have hm := mul_le_mul_of_nonneg_right htail
      (by positivity : (0 : ℤ) ≤ (C * R : ℕ) + (R : ℤ))
    change |(F.modulus w : ℤ) * alignmentIntegerArrayProgression Δ T u| ≤ (R : ℤ) at hprog
    change |alignmentIntegerSlotShift ρ v| ≤ (R : ℤ) at hslot
    push_cast at hb hm ⊢
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (L : ℤ) - 1) (Int.natCast_nonneg R)]
  have htotal : |alignmentIntegerArrayArgument y (F.modulus w) ρ Δ T p v u -
      ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ)| ≤ ((C + 3) * L * R : ℕ) := by
    have hh := abs_add_le
      (alignmentIntegerArrayArgument y (F.modulus w) ρ Δ T p v u -
        (alignmentNaturalBlockProduct y T : ℤ) * y i)
      (((alignmentNaturalBlockProduct y T * y i : ℕ) : ℤ) -
        ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ))
    rw [Nat.cast_mul, sub_add_sub_cancel] at hh
    have hd : _ ≤ ((L * R : ℕ) : ℤ) := hdist
    have hb := hh.trans (add_le_add hlocal hd)
    calc
      _ ≤ (((C + 2) * L * R : ℕ) : ℤ) + ((L * R : ℕ) : ℤ) := hb
      _ = _ := by push_cast; ring
  have hh := intervalInteriorRoot_shift_quotient (F.gap w i.val) ((C + 3) * L * R)
    (hF.gap_positive w i.val) _ _ hinterior htotal
  simpa only [add_sub_cancel] using hh

end Hindman168
