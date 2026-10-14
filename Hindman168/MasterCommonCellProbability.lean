import Hindman168.MasterCommonCyclicShortCube

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.common_cell_probability_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val) :
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let W := primorial w
      let M := (F.modulus w : ℕ)
      let R := F.gap w (gap w).val
      let l := (X : ℤ) / R + 1
      let u := ((X ^ 2 : ℕ) : ℤ) / R
      let I := Finset.Ico (l * R) (u * R)
      let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
      let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
        (∑ y ∈ I, integerMass X W y)
      (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1 := by
  classical
  filter_upwards [hF.aligned_interior_mass_eventually_positive gap pivot horder,
    hF.primorial_dvd_modulus] with w hp hWM
  let X := F.cutoff w (pivot w).val
  let W := primorial w
  let M := (F.modulus w : ℕ)
  let R := F.gap w (gap w).val
  let l := (X : ℤ) / R + 1
  let u := ((X ^ 2 : ℕ) : ℤ) / R
  let I := Finset.Ico (l * R) (u * R)
  let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
  let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
    (∑ y ∈ I, integerMass X W y)
  change (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1
  refine ⟨fun _ => integerMass_cell_probability_nonneg X W _ _ hp, ?_⟩
  have hwid : M * (R / M) = R := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  have hend := alignedInterior_endpoint_bounds (X : ℤ) (X ^ 2 : ℕ) R (hF.gap_positive w (gap w).val)
  have hs := alignedInterval_cell_probability_sum X W M (R / M) (F.modulus w).pos
    (hF.common_cyclic_order_positive w (gap w).val) hWM l u
    (by simpa only [hwid] using hend.1) (by simpa only [hwid] using hend.2.2.2)
    (by simpa only [hwid] using hp)
  simp only [hwid] at hs
  dsimp only [p]
  rw [Finset.sum_coe_sort C (fun c : ℤ × Fin M =>
    (∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y) / (∑ y ∈ I, integerMass X W y))]
  dsimp only [C]
  exact (Finset.sum_product (Finset.Ico l u)
    ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
    (fun c : ℤ × Fin M => (∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, integerMass X W y) /
      (∑ y ∈ I, integerMass X W y))).trans hs

theorem constructedMasterFamily_actual_cell_subgroup_gowers_eventually
    {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (ε : ℝ) (hε : 0 < ε) :
    let F := constructedMasterFamily N D hD
    let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let W := primorial w
      let M := (F.modulus w : ℕ)
      let R := F.gap w (gap w).val
      let q := R / M
      letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
      let l := (X : ℤ) / R + 1
      let u := ((X ^ 2 : ℕ) : ℤ) / R
      let I := Finset.Ico (l * R) (u * R)
      let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
      let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
        (∑ y ∈ I, integerMass X W y)
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
      ∀ d : ℕ, 0 < d → ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      let h := fun (c : C) (z : ZMod q) => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)
      expectation (tensor μ μ) (fun xy => weightedSubgroupGowersValue
        (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol xy.1).natAbs / M) ⊔
          multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol xy.2).natAbs / M)) p d h) ≤
        weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p d h + ε := by
  classical
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  filter_upwards [hF.common_cell_probability_eventually gap pivot horder,
    constructedMasterFamily_conditioned_subgroup_gowers_eventually N D hD pol hpol T hT
      (fun w => (gap w).val) ε hε] with w hp hb
  dsimp only
  intro d hd f hf
  exact hb _ _ ((constructedMasterFamily N D hD).modulus w).pos
    (hF.common_cyclic_order_positive w (gap w).val) _ _ hp.1 hp.2 d hd _ (fun _ _ => hf _)

end Hindman168
