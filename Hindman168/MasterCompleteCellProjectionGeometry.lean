import Hindman168.MasterCommonCellProbability

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical

/-- The original admissible complete cells between the aligned endpoints. -/
noncomputable def masterCompleteCells {N : ℕ} (F : MasterParameterFamily)
    (gap pivot : ℕ → Fin N) (w : ℕ) : Finset (ℤ × Fin (F.modulus w : ℕ)) :=
  let X := F.cutoff w (pivot w).val
  let R := F.gap w (gap w).val
  (Finset.Ico ((X : ℤ) / R + 1) (((X ^ 2 : ℕ) : ℤ) / R)).product
    ((Finset.univ : Finset (Fin (F.modulus w : ℕ))).filter (fun r => r.val.Coprime (primorial w)))

theorem MasterParameterConditions.complete_cell_projection_geometry
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let W := primorial w
      let M := (F.modulus w : ℕ)
      let q := F.gap w (gap w).val / M
      0 < X ∧ 0 < M ∧ W ∣ M ∧ 0 < harmonicNormalizer X W ∧
      F.gap w (gap w).val = M * q ∧ ∀ c ∈ masterCompleteCells F gap pivot w,
        c.2.val.Coprime W ∧ (X : ℤ) ≤ c.1 * (M * q : ℕ) ∧
          c.1 * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ) := by
  filter_upwards [hF.nil_boundary_raw_geometry pivot, hF.primorial_dvd_modulus] with w hx hWM
  let X := F.cutoff w (pivot w).val
  let M := (F.modulus w : ℕ)
  let R := F.gap w (gap w).val
  let q := R / M
  have he : M * q = R := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  have hz := (harmonicNormalizer_boundary_lower hx.1 (primorial_pos w) hx.2.1 hx.2.2).1
  refine ⟨by omega, (F.modulus w).pos, hWM, hz, he.symm, ?_⟩
  intro c hc
  obtain ⟨hk, hr⟩ := Finset.mem_product.mp hc
  have hcop := (Finset.mem_filter.mp hr).2
  obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hk
  have hend := alignedInterior_endpoint_bounds (X : ℤ) (X ^ 2 : ℕ) R
    (hF.gap_positive w (gap w).val)
  refine ⟨hcop, ?_, ?_⟩
  · change (X : ℤ) ≤ c.1 * (M * q : ℕ)
    rw [he]
    exact hend.1.trans (mul_le_mul_of_nonneg_right hl (Int.natCast_nonneg R))
  · change c.1 * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ)
    rw [he, ← add_one_mul]
    change c.1 < ((X ^ 2 : ℕ) : ℤ) / R at hu
    have hk1 : c.1 + 1 ≤ ((X ^ 2 : ℕ) : ℤ) / R := by omega
    exact (mul_le_mul_of_nonneg_right hk1 (Int.natCast_nonneg R)).trans hend.2.2.2

theorem MasterParameterConditions.complete_cell_mass_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    Tendsto (fun w => ∑ c : masterCompleteCells F gap pivot w,
      ∑ y ∈ intervalResidueSet
        (c.val.1 * ((F.modulus w : ℕ) * (F.gap w (gap w).val / (F.modulus w : ℕ)) : ℕ))
        ((F.modulus w : ℕ) * (F.gap w (gap w).val / (F.modulus w : ℕ)))
        (F.modulus w : ℕ) c.val.2.val,
          integerMass (F.cutoff w (pivot w).val) (primorial w) y) atTop (𝓝 1) := by
  apply (hF.aligned_interior_mass_tendsto gap pivot horder).congr'
  filter_upwards [hF.primorial_dvd_modulus] with w hWM
  let X := F.cutoff w (pivot w).val
  let M := (F.modulus w : ℕ)
  let R := F.gap w (gap w).val
  let q := R / M
  have he : M * q = R := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  have hend := alignedInterior_endpoint_bounds (X : ℤ) (X ^ 2 : ℕ) R
    (hF.gap_positive w (gap w).val)
  have hs := alignedInterval_admissible_cell_sum X (primorial w) M q (F.modulus w).pos
    (hF.common_cyclic_order_positive w (gap w).val) hWM
    ((X : ℤ) / R + 1) (((X ^ 2 : ℕ) : ℤ) / R)
    (by simpa only [he] using hend.1) (by simpa only [he] using hend.2.2.2) (fun _ => 1)
  simp only [mul_one, he] at hs
  change (∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
    integerMass X (primorial w) y) = _
  rw [Finset.sum_coe_sort (masterCompleteCells F gap pivot w) (fun c : ℤ × Fin M =>
    ∑ y ∈ intervalResidueSet (c.1 * (M * q : ℕ)) (M * q) M c.2.val,
      integerMass X (primorial w) y)]
  dsimp only [masterCompleteCells]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simpa only [he] using hs

theorem MasterParameterConditions.complete_cell_scale_ratio_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    Tendsto (fun w => ((F.modulus w : ℕ) * (F.gap w (gap w).val / (F.modulus w : ℕ)) : ℕ) /
      (F.cutoff w (pivot w).val : ℝ)) atTop (𝓝 0) := by
  have hK : ∀ᶠ w in atTop, 1 ≤ F.auxiliary w (gap w).val :=
    Eventually.of_forall (fun w => by have hh := F.auxiliary_ge_two w (gap w).val; omega)
  have ht := hF.nil_boundary_endpoint_ratio_tendsto gap pivot (fun _ => 1) horder hK
  apply squeeze_zero' (Eventually.of_forall (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _ ht
  apply Eventually.of_forall
  intro w
  have he : (F.modulus w : ℕ) * (F.gap w (gap w).val / (F.modulus w : ℕ)) =
      F.gap w (gap w).val := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  rw [he]
  simp only [mul_one]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hW : (1 : ℝ) ≤ primorial w := by exact_mod_cast primorial_pos w
  have hR := Nat.cast_nonneg (α := ℝ) (F.gap w (gap w).val)
  nlinarith

end Hindman168
