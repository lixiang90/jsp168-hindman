import Hindman168.MasterCompleteCellLawIdentities

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical

/-- The actual master complete-cell mass, in the M*q coordinates used
by the inverse argument. -/
noncomputable def masterCompleteCellMass {N : ℕ} (F : MasterParameterFamily)
    (gap pivot : ℕ → Fin N) (w : ℕ) (c : masterCompleteCells F gap pivot w) : ℝ :=
  let M := (F.modulus w : ℕ)
  let q := F.gap w (gap w).val / M
  ∑ y ∈ intervalResidueSet (c.val.1 * (M * q : ℕ)) (M * q) M c.val.2.val,
    integerMass (F.cutoff w (pivot w).val) (primorial w) y

noncomputable def masterCompleteCellProbability {N : ℕ} (F : MasterParameterFamily)
    (gap pivot : ℕ → Fin N) (w : ℕ) (c : masterCompleteCells F gap pivot w) : ℝ :=
  masterCompleteCellMass F gap pivot w c / ∑ a, masterCompleteCellMass F gap pivot w a

/-- The original weighted global norm, retaining the actual complete-cell
probabilities. This definition asserts no inverse-theorem conclusion. -/
noncomputable def masterCompleteGlobalGowersValue {N : ℕ} (F : MasterParameterFamily)
    (gap pivot : ℕ → Fin N) (w d : ℕ)
    [NeZero (F.gap w (gap w).val / (F.modulus w : ℕ))] (f : ℤ → ℝ) : ℝ :=
  let M := (F.modulus w : ℕ)
  let q := F.gap w (gap w).val / M
  weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q))
    (masterCompleteCellProbability F gap pivot w) d (fun c z =>
      f (c.val.1 * (M * q : ℕ) + c.val.2.val + (M : ℤ) * z.val))

/-- Exact equality of the probability functions, including every original
cell coefficient and the original finite-stage denominator. -/
theorem MasterParameterConditions.canonical_cell_probability_eq_aligned_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let R := F.gap w (gap w).val
      masterCompleteCellProbability F gap pivot w =
        (fun c : masterCompleteCells F gap pivot w =>
          (∑ y ∈ intervalResidueSet (c.val.1 * R) R (F.modulus w : ℕ) c.val.2.val,
            integerMass X (primorial w) y) /
          (∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
            integerMass X (primorial w) y)) := by
  filter_upwards [hF.complete_cell_mass_eq_interior_eventually gap pivot] with w hw
  have he : (F.modulus w : ℕ) * (F.gap w (gap w).val / (F.modulus w : ℕ)) =
      F.gap w (gap w).val := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  funext c
  dsimp only [masterCompleteCellProbability, masterCompleteCellMass]
  rw [he, hw]

/-- The inverse argument and the original short-cube Bessel estimate use
exactly the same finite-stage probability law and cell functions. -/
theorem MasterParameterConditions.canonical_global_gowers_eq_aligned_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let M := (F.modulus w : ℕ)
      let R := F.gap w (gap w).val
      let q := R / M
      letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
      let I := Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R)
      let p := fun c : masterCompleteCells F gap pivot w =>
        (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X (primorial w) y) /
          (∑ y ∈ I, integerMass X (primorial w) y)
      ∀ d (f : ℤ → ℝ), masterCompleteGlobalGowersValue F gap pivot w d f =
        weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p d
          (fun c z => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)) := by
  filter_upwards [hF.canonical_cell_probability_eq_aligned_eventually gap pivot] with w hw
  dsimp only
  letI : NeZero (F.gap w (gap w).val / (F.modulus w : ℕ)) :=
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  intro d f
  have he : (F.modulus w : ℕ) * (F.gap w (gap w).val / (F.modulus w : ℕ)) =
      F.gap w (gap w).val := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  dsimp only [masterCompleteGlobalGowersValue]
  rw [he, hw]

end Hindman168
