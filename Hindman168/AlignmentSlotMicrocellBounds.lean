import Hindman168.MasterMicrocellGrowth
import Hindman168.AlignmentIntegerSlotShifts

/-! Every fixed finite slot table is uniformly negligible relative to the
actual microcell width, for all canonical residue representatives at once. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem alignmentIntegerSlotWeight_nonneg {n : ℕ} {i : Fin n}
    (v : AlignmentAddingPair n i → ℤ) : 0 ≤ alignmentIntegerSlotWeight v := by
  letI := alignmentAddingPairFintype n i
  unfold alignmentIntegerSlotWeight
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem alignment_slot_microcell_uniform_small
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n)
    (V : Finset (AlignmentAddingPair n i → ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ v ∈ V, ∀ ρ : AlignmentAddingPair n i → ℕ,
      (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) →
      |(alignmentIntegerSlotShift ρ v : ℝ)| ≤
        ε * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by
  apply (eventually_all_finset V).mpr
  intro v _
  filter_upwards [master_microcell_eventually_polynomial_small hF (fun _ => i) 2
    (alignmentIntegerSlotWeight v : ℝ) hε] with w hw
  intro ρ hρ
  have hb := alignmentIntegerSlotShift_bound ρ v ((F.modulus w : ℕ) ^ 2) hρ
  have hbR : |(alignmentIntegerSlotShift ρ v : ℝ)| ≤
      (F.modulus w : ℝ) ^ 2 * (alignmentIntegerSlotWeight v : ℝ) := by exact_mod_cast hb
  have hm : (F.modulus w : ℝ) ^ 2 ≤ (F.auxiliary w i.val : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left (F.modulus_le_auxiliary w i.val) 2
  have hv : (0 : ℝ) ≤ alignmentIntegerSlotWeight v := by
    exact_mod_cast alignmentIntegerSlotWeight_nonneg v
  have hm' := mul_le_mul_of_nonneg_right hm hv
  calc
    _ ≤ (F.modulus w : ℝ) ^ 2 * (alignmentIntegerSlotWeight v : ℝ) := hbR
    _ ≤ (F.auxiliary w i.val : ℝ) ^ 2 * (alignmentIntegerSlotWeight v : ℝ) := hm'
    _ = (alignmentIntegerSlotWeight v : ℝ) * (F.auxiliary w i.val : ℝ) ^ 2 := mul_comm _ _
    _ ≤ _ := hw

theorem alignment_slot_microcell_uniform_margin
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n)
    (V : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ v ∈ V, ∀ ρ : AlignmentAddingPair n i → ℕ,
      (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) →
      |alignmentIntegerSlotShift ρ v| ≤
        (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ) := by
  filter_upwards [alignment_slot_microcell_uniform_small hF i V (by norm_num : (0 : ℝ) < 1)]
    with w hw
  intro v hv ρ hρ
  have hh := hw v hv ρ hρ
  rw [one_mul] at hh
  exact_mod_cast hh

end Hindman168
