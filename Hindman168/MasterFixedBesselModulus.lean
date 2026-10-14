import Hindman168.MasterCanonicalGlobalGowers
import Hindman168.MasterActualCellBessel

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- A fixed universal Bessel modulus budget may be chosen before any
master count, polynomial data, gap, cyclic group or cell probabilities. -/
theorem constructedMasterFamily_conditioned_bessel_of_modulus_eventually
    {a n : ℕ} (N : ℕ) (D : Finset (MvPolynomial (Fin a) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (gap : ℕ → ℕ) (d : ℕ) (hd : 0 < d) (θ η : ℝ) (hθ : 0 < θ)
    (hmod : finiteWeightedBesselModulus d (2 * θ) < η) :
    ∀ᶠ w in atTop,
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (gap w))) (primeSampleGood T)
      ∀ (M q : ℕ), 0 < M → ∀ (hq : 0 < q),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      ∀ (κ : Type) [Fintype κ] (p : κ → ℝ), (∀ c, 0 ≤ p c) → (∑ c, p c = 1) →
      ∀ f : κ → ZMod q → ℝ, (∀ c z, |f c z| ≤ 1) →
      weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p (d + d - 1) f ≤ θ →
        expectation μ (fun x => weightedSubgroupGowersValue
          (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol x).natAbs / M)) p d f) < η := by
  have hrough := constructedMasterFamily_conditioned_subgroup_gowers_eventually
    N D hD pol hpol T hT gap θ hθ
  have htotal := constructedMasterFamily_primeGoodSample_tendsto_one N D hD T hT gap
  filter_upwards [hrough, htotal.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with w hw ht
  dsimp only
  intro M q hM hq
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  intro κ _ p hp hs f hf hglobal
  let μ := conditionMass (dyadicPoolTupleMass
    (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (gap w))) (primeSampleGood T)
  have hμ : ∀ x, 0 ≤ μ x := conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg _)
  have htμ : total μ = 1 := conditionMass_total _ _ ht
  have hpair := hw M q hM hq κ p hp hs (d + d - 1) (by omega) f hf
  have hbudget : expectation (tensor μ μ) (fun xy => weightedSubgroupGowersValue
      (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol xy.1).natAbs / M) ⊔
        multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol xy.2).natAbs / M))
      p (d + d - 1) f) ≤ 2 * θ := hpair.trans (by linarith)
  exact (finiteMass_weighted_subgroup_qualitative_bessel p hp hs μ hμ htμ
    (fun x => multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol x).natAbs / M))
    f hf d hd (2 * θ) hbudget).trans_lt hmod

/-- The same fixed budget applies to the actual original master cells
with the canonical probability law used by the inverse argument. -/
theorem constructedMasterFamily_canonical_cell_bessel_of_modulus_eventually
    {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (d : ℕ) (hd : 0 < d) (θ η : ℝ) (hθ : 0 < θ)
    (hmod : finiteWeightedBesselModulus d (2 * θ) < η) :
    let F := constructedMasterFamily N D hD
    let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
    ∀ᶠ w in atTop,
      let M := (F.modulus w : ℕ)
      let q := F.gap w (gap w).val / M
      letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
      ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      masterCompleteGlobalGowersValue F gap pivot w (d + d - 1) f ≤ θ →
        expectation μ (fun x => weightedSubgroupGowersValue
          (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol x).natAbs / M))
          (masterCompleteCellProbability F gap pivot w) d (fun c z =>
            f (c.val.1 * (M * q : ℕ) + c.val.2.val + (M : ℤ) * z.val))) < η := by
  let F := constructedMasterFamily N D hD
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  have hb := constructedMasterFamily_conditioned_bessel_of_modulus_eventually N D hD
    pol hpol T hT (fun w => (gap w).val) d hd θ η hθ hmod
  filter_upwards [hF.common_cell_probability_eventually gap pivot horder,
    hF.complete_cell_mass_eq_interior_eventually gap pivot, hb] with w hp hm hw
  dsimp only
  let M := (F.modulus w : ℕ)
  let q := F.gap w (gap w).val / M
  letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  have he : M * q = F.gap w (gap w).val :=
    Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  have hprob : (∀ c, 0 ≤ masterCompleteCellProbability F gap pivot w c) ∧
      ∑ c, masterCompleteCellProbability F gap pivot w c = 1 := by
    dsimp only [masterCompleteCellProbability, masterCompleteCellMass]
    rw [he, hm]
    exact hp
  intro f hf hg
  exact hw M q (F.modulus w).pos (hF.common_cyclic_order_positive w (gap w).val)
    (masterCompleteCells F gap pivot w) (masterCompleteCellProbability F gap pivot w)
    hprob.1 hprob.2 _ (fun _ _ => hf _) hg

end Hindman168
