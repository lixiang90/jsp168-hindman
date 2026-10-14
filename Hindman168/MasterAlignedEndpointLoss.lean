import Hindman168.AlignedInteriorMassCrude

namespace Hindman168
open Filter
open scoped BigOperators Topology

theorem MasterParameterConditions.aligned_endpoint_loss_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    Tendsto (fun w =>
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      ∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
        Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
        integerMass X (primorial w) y) atTop (𝓝 0) := by
  have hk : ∀ᶠ w in atTop, 1 ≤ F.auxiliary w (gap w).val :=
    Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w (gap w).val; omega)
  have he := (hF.nil_boundary_endpoint_ratio_tendsto gap pivot (fun _ => 1) horder hk).const_mul 2
  simp only [mul_one, mul_zero] at he
  apply squeeze_zero' (Eventually.of_forall (fun w =>
    Finset.sum_nonneg (fun y _ => integerMass_nonnegative _ _ y))) _ he
  filter_upwards [hF.nil_boundary_raw_geometry pivot] with w hw
  exact alignedInterior_deleted_integerMass_crude hw.1 (primorial_pos w)
    (hF.gap_positive w (gap w).val) hw.2.1 hw.2.2

theorem MasterParameterConditions.aligned_endpoint_test_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (f : ℕ → ℤ → ℝ) (hf : ∀ w y, |f w y| ≤ 1) :
    Tendsto (fun w =>
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      |∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
        Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
        integerMass X (primorial w) y * f w y|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
    (hF.aligned_endpoint_loss_tendsto gap pivot horder)
  apply Eventually.of_forall
  intro w
  dsimp only
  calc
    _ ≤ ∑ y ∈ _, |integerMass _ (primorial w) y * f w y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (integerMass_nonnegative _ _ y)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf w y) (integerMass_nonnegative _ _ y)

end Hindman168
