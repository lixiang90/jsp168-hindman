import Hindman168.MasterCommonCellProbability
import Hindman168.MasterQualitativeSubgroupBessel

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- The proved Bessel step for the paper's actual harmonic cyclic cells
and conditioned prime tuples. Their exact cell probabilities, common
cyclic order, polynomial subgroup directions and integer input are retained. -/
theorem constructedMasterFamily_actual_cell_bessel_eventually
    {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    let F := constructedMasterFamily N D hD
    let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ w in atTop,
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
      ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      let h := fun (c : C) (z : ZMod q) => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)
      weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p (d + d - 1) h ≤ θ →
        expectation μ (fun x => weightedSubgroupGowersValue
          (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol x).natAbs / M))
          p d h) < ε := by
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  obtain ⟨θ, hθ, hb⟩ := constructedMasterFamily_conditioned_subgroup_bessel_eventually
    N D hD pol hpol T hT (fun w => (gap w).val) d hd ε hε
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [hF.common_cell_probability_eventually gap pivot horder, hb] with w hp hw
  dsimp only
  intro f hf
  exact hw _ _ ((constructedMasterFamily N D hD).modulus w).pos
    (hF.common_cyclic_order_positive w (gap w).val) _ _ hp.1 hp.2 _ (fun _ _ => hf _)

end Hindman168
