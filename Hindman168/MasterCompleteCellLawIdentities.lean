import Hindman168.MasterCompleteCellProjectionGeometry

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical

/-- At each admissible stage, the sum of original complete-cell masses
is exactly the aligned interior mass, not just asymptotically equal. -/
theorem MasterParameterConditions.complete_cell_mass_eq_interior_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      (∑ c : masterCompleteCells F gap pivot w,
        ∑ y ∈ intervalResidueSet (c.val.1 * R) R (F.modulus w : ℕ) c.val.2.val,
          integerMass X (primorial w) y) =
      ∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
        integerMass X (primorial w) y := by
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
  dsimp only
  rw [Finset.sum_coe_sort (masterCompleteCells F gap pivot w) (fun c : ℤ × Fin M =>
    ∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X (primorial w) y)]
  dsimp only [masterCompleteCells]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  exact hs.symm

end Hindman168
