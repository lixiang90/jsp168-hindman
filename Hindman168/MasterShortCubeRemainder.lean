import Hindman168.FullWindowShortCubeBound

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem MasterParameterConditions.cell_width_cutoff_ratio_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    Tendsto (fun w => (F.gap w (gap w).val : ℝ) / F.cutoff w (pivot w).val) atTop (𝓝 0) := by
  have hk : ∀ᶠ w in atTop, 1 ≤ F.auxiliary w (gap w).val :=
    Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w (gap w).val; omega)
  have he := hF.nil_boundary_endpoint_ratio_tendsto gap pivot (fun _ => 1) horder hk
  simp only [mul_one] at he
  apply squeeze_zero' (Eventually.of_forall (fun w => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _ he
  apply Eventually.of_forall
  intro w
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hw : (1 : ℝ) ≤ primorial w := by exact_mod_cast Nat.succ_le_of_lt (primorial_pos w)
  have hr := Nat.cast_nonneg (α := ℝ) (F.gap w (gap w).val)
  nlinarith

theorem MasterParameterConditions.shortCube_fullWindow_remainder_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    Tendsto (fun w =>
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      (R : ℝ) / X + 2 * ∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
        Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
        integerMass X (primorial w) y) atTop (𝓝 0) := by
  have h1 := hF.cell_width_cutoff_ratio_tendsto gap pivot horder
  have h2 := (hF.aligned_endpoint_loss_tendsto gap pivot horder).const_mul 2
  simpa only [mul_zero, add_zero] using h1.add h2

end Hindman168
