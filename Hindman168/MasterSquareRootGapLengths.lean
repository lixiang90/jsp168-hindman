import Hindman168.MasterTranslationScales

/-!
# Concrete uniform lower lengths for actual master gaps

A polynomial upper cap on replica moduli gives the original shift length
R / cap and the auxiliary length floor(sqrt(R / cap)). Their every-power
growth follows from the master gap condition, including varying finite
gap labels. The actual prime-dependent quotients are larger whenever the
cap bounds their denominator.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology Classical

def masterShiftLengthLowerBound (F : MasterParameterFamily) (w j k : ℕ) : ℕ :=
  F.gap w j / ((F.pool w j).upper + F.auxiliary w j) ^ k

theorem MasterParameterConditions.quotient_shift_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) (k : ℕ) :
    PowerDominates atTop (fun w => (masterShiftLengthLowerBound F w (index w).val k : ℝ))
      (fun w => ((F.pool w (index w).val).upper + F.auxiliary w (index w).val : ℝ)) := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) index
  apply hg.nat_div k
  · exact Eventually.of_forall (fun w => by
      have hh := F.auxiliary_ge_two w (index w).val
      have hr : (2 : ℝ) ≤ F.auxiliary w (index w).val := by exact_mod_cast hh
      linarith [Nat.cast_nonneg (F.pool w (index w).val).upper (α := ℝ)])
  · apply Eventually.of_forall
    intro w
    have hp : 0 < (F.pool w (index w).val).upper + F.auxiliary w (index w).val := by
      have hh := F.auxiliary_ge_two w (index w).val
      omega
    exact ⟨pow_pos hp k, by norm_cast⟩

theorem MasterParameterConditions.quotient_sqrt_sampling_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) (k : ℕ)
    {V : ℕ → ℕ} (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (index w).val) :
    PowerDominates atTop
      (fun w => (Nat.sqrt (masterShiftLengthLowerBound F w (index w).val k) : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)) := by
  have hg := (hF.quotient_shift_growth index k).nat_sqrt
    (Eventually.of_forall (fun w => by positivity))
  apply hg.mono_base 3
  filter_upwards [hV] with w hVw
  let S := (F.pool w (index w).val).upper + F.auxiliary w (index w).val
  have hS : 2 ≤ S := by have hh := F.auxiliary_ge_two w (index w).val; omega
  have hVS : V w ≤ S := by omega
  have hs : samplingSize 0 (V w) 0 (V w) ≤ S ^ 3 := by
    have hsq : 3 ≤ S ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul_right S hsq
    rw [← pow_succ] at hm
    change 3 * S ≤ S ^ 3 at hm
    unfold samplingSize
    omega
  exact ⟨Nat.cast_nonneg _, by positivity, by exact_mod_cast hs⟩

theorem masterShiftLengthLowerBound_le_actual (F : MasterParameterFamily)
    (w j k J M : ℕ) (hden : 0 < J * M)
    (hcap : J * M ≤ ((F.pool w j).upper + F.auxiliary w j) ^ k) :
    masterShiftLengthLowerBound F w j k ≤ F.gap w j / (J * M) := by
  unfold masterShiftLengthLowerBound
  exact Nat.div_le_div_left hcap hden

theorem actual_shift_modulus_length_bound (R J M : ℕ) (hJ : 1 ≤ J) :
    M * (R / (J * M)) ≤ R := by
  have hc : M ≤ J * M := by nlinarith
  exact (Nat.mul_le_mul_right (R / (J * M)) hc).trans (Nat.mul_div_le R (J * M))

end Hindman168
