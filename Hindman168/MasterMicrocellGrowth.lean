import Hindman168.AlignedSqrtMicrocellGrowth
import Hindman168.MasterShortBinCutoffDiscard

/-! The actual master modulus and gap give the paper's exact aligned
microcell and progression lengths, both dominating every auxiliary power. -/

namespace Hindman168

open Filter
open scoped Topology

theorem master_microcell_growth
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) :
    PowerDominates atTop
      (fun w => (alignedSqrtMicrocellWidth (F.gap w (pivot w).val) (F.modulus w) : ℝ))
      (fun w => (F.auxiliary w (pivot w).val : ℝ)) ∧
    PowerDominates atTop
      (fun w => (Nat.sqrt (F.gap w (pivot w).val) / (F.modulus w : ℕ) : ℕ))
      (fun w => (F.auxiliary w (pivot w).val : ℝ)) := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) pivot
  have hga : PowerDominates atTop (fun w => (F.gap w (pivot w).val : ℝ))
      (fun w => (F.auxiliary w (pivot w).val : ℝ)) := by
    apply hg.mono_base 1
    exact Eventually.of_forall (fun w => ⟨Nat.cast_nonneg _, by positivity, by
      simp only [pow_one]; linarith [Nat.cast_nonneg (α := ℝ) (F.pool w (pivot w).val).upper]⟩)
  have hQ : ∀ᶠ w in atTop, (2 : ℝ) ≤ F.auxiliary w (pivot w).val :=
    Eventually.of_forall (fun w => by exact_mod_cast F.auxiliary_ge_two w (pivot w).val)
  have hM : ∀ᶠ w in atTop, 0 < (F.modulus w : ℕ) ∧
      (F.modulus w : ℝ) ≤ (F.auxiliary w (pivot w).val : ℝ) ^ 1 :=
    Eventually.of_forall (fun w => ⟨(F.modulus w).pos, by
      rw [pow_one]; exact_mod_cast F.modulus_le_auxiliary w (pivot w).val⟩)
  exact ⟨alignedSqrtMicrocellWidth_growth _ _ _ hga 1 hQ hM,
    alignedSqrtMicrocellLength_growth _ _ _ hga 1 hQ hM⟩

theorem master_microcell_eventually_positive
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) :
    ∀ᶠ w in atTop, 0 < alignedSqrtMicrocellWidth (F.gap w (pivot w).val) (F.modulus w) := by
  have hh := (master_microcell_growth hF pivot).1.eventually_bound
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) 0 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh] with w hw
  simp only [pow_zero, mul_one] at hw
  have hwN : 1 ≤ alignedSqrtMicrocellWidth (F.gap w (pivot w).val) (F.modulus w) := by exact_mod_cast hw
  exact hwN

theorem master_microcell_polynomial_ratio_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) (p : ℕ) (C : ℝ) :
    Tendsto (fun w => C * (F.auxiliary w (pivot w).val : ℝ) ^ p /
      alignedSqrtMicrocellWidth (F.gap w (pivot w).val) (F.modulus w)) atTop (𝓝 0) := by
  have hh := (((master_microcell_growth hF pivot).1 p).tendsto_div_nhds_zero).const_mul C
  simpa only [mul_div_assoc, mul_zero] using hh

theorem master_microcell_eventually_polynomial_small
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) (p : ℕ) (C : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, C * (F.auxiliary w (pivot w).val : ℝ) ^ p ≤
      ε * alignedSqrtMicrocellWidth (F.gap w (pivot w).val) (F.modulus w) := by
  filter_upwards [(master_microcell_polynomial_ratio_tendsto hF pivot p C).eventually (gt_mem_nhds hε),
    master_microcell_eventually_positive hF pivot] with w hw hr
  have hrR : (0 : ℝ) < alignedSqrtMicrocellWidth (F.gap w (pivot w).val) (F.modulus w) := by
    exact_mod_cast hr
  exact (div_le_iff₀ hrR).mp hw.le

end Hindman168
