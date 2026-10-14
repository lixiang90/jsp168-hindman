import Hindman168.MasterSubgroupCombination
import Hindman168.FiniteMassWeightedSubgroupBessel

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- Rough coprimality and the proved qualitative Bessel modulus control
the original good-tuple weighted local norms by one global norm threshold.
The eventual estimate is uniform over the cyclic modulus, original cell
law and every actual unit input. No Bessel theorem is supplied as a premise. -/
theorem constructedMasterFamily_conditioned_subgroup_bessel_eventually
    {a n : ℕ} (N : ℕ) (D : Finset (MvPolynomial (Fin a) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ g ∈ T, g ≠ 0)
    (l : ℕ → ℕ) (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ w in atTop,
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w))) (primeSampleGood T)
      ∀ (M q : ℕ), 0 < M → ∀ (hq : 0 < q),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      ∀ (κ : Type) [Fintype κ] (p : κ → ℝ), (∀ c, 0 ≤ p c) → (∑ c, p c = 1) →
      ∀ h : κ → ZMod q → ℝ, (∀ c z, |h c z| ≤ 1) →
      weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p (d + d - 1) h ≤ θ →
        expectation μ (fun x => weightedSubgroupGowersValue
          (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f x).natAbs / M))
          p d h) < ε := by
  obtain ⟨δ, hδ, hb⟩ := finiteWeightedBesselModulus_uniform_small d hd ε hε
  have hrough := constructedMasterFamily_conditioned_subgroup_gowers_eventually
    N D hD f hf T hT l (δ / 2) (by positivity)
  have htotal := constructedMasterFamily_primeGoodSample_tendsto_one N D hD T hT l
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hrough, htotal.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with w hw ht
  dsimp only
  intro M q hM hq
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  intro κ _ p hp hs h hh hglobal
  let μ := conditionMass (dyadicPoolTupleMass
    (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w))) (primeSampleGood T)
  have hμ : ∀ x, 0 ≤ μ x := conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg _)
  have htμ : total μ = 1 := conditionMass_total _ _ ht
  have hpair := hw M q hM hq κ p hp hs (d + d - 1) (by omega) h hh
  have hpδ : expectation (tensor μ μ) (fun xy => weightedSubgroupGowersValue
      (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f xy.1).natAbs / M) ⊔
        multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f xy.2).natAbs / M))
      p (d + d - 1) h) ≤ δ := by
    exact hpair.trans (by linarith)
  exact (finiteMass_weighted_subgroup_qualitative_bessel p hp hs μ hμ htμ
    (fun x => multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f x).natAbs / M))
    h hh d hd δ hpδ).trans_lt (hb δ le_rfl)

end Hindman168
