import Hindman168.MasterRoughCoprimality
import Hindman168.PredictionQuotientLengths
import Hindman168.SubgroupGowersWeightedBounds
import Hindman168.FiniteCountableExpectations
import Hindman168.FiniteWeightedErrors
import Hindman168.FiniteEventComparison

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

theorem predictionCubeModulus_quotient_rough {n : ℕ} (w M : ℕ) (hM : 0 < M)
    (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ) :
    (predictionCubeModulus w M f x).natAbs / M =
      roughPartNat w (MvPolynomial.eval (fun j => (x j : ℤ)) f).natAbs := by
  rw [predictionCubeModulus_natAbs, Nat.mul_div_cancel_left _ hM]

theorem finiteMass_good_event_statistic_bound {ι : Type*} (μ : Mass ι)
    (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) (E : ι → Prop)
    (f : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ x, f x ≤ 1) (hgood : ∀ x, E x → f x ≤ c) :
    expectation μ f ≤ c + (1 - event μ E) := by
  have h := expectation_mono μ f (fun x => c + if ¬ E x then 1 else 0) hμ (fun x => by
    by_cases hx : E x
    · simpa only [hx, not_true_eq_false, if_false, add_zero] using hgood x hx
    · simpa only [hx, not_false_eq_true, if_true] using (hf x).trans (by linarith))
  rw [expectation_add, expectation_const, ht, one_mul] at h
  calc
    _ ≤ c + expectation μ (fun x => if ¬ E x then 1 else 0) := h
    _ = c + event μ (fun x => ¬ E x) := by
      congr 1
      simp only [expectation, event, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by rw [event_complement, ht]

theorem constructedMasterFamily_conditioned_subgroup_gowers_eventually
    {a n : ℕ} (N : ℕ) (D : Finset (MvPolynomial (Fin a) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ g ∈ T, g ≠ 0)
    (l : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in atTop,
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w))) (primeSampleGood T)
      ∀ (M q : ℕ), 0 < M → ∀ (hq : 0 < q),
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      ∀ (κ : Type) [Fintype κ] (α : κ → ℝ), (∀ c, 0 ≤ α c) → (∑ c, α c = 1) →
      ∀ (d : ℕ), 0 < d → ∀ h : κ → ZMod q → ℝ, (∀ c z, |h c z| ≤ 1) →
      expectation (tensor μ μ) (fun xy => weightedSubgroupGowersValue
        (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f xy.1).natAbs / M) ⊔
          multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f xy.2).natAbs / M)) α d h) ≤
        weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) α d h + ε := by
  have hgood := constructedMasterFamily_goodSample_conditioned_rough_tendsto_one
    N D hD hf hf T hT T hT l l
  have htotal := constructedMasterFamily_primeGoodSample_tendsto_one N D hD T hT l
  have herr := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgood)
  have herr' : ∀ᶠ w in atTop, 1 - event
      (tensor (conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w))) (primeSampleGood T))
        (conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w))) (primeSampleGood T)))
      (roughPolynomialGoodEvent w f f) < ε := by
    exact (show Tendsto _ atTop (𝓝 (0 : ℝ)) by simpa only [sub_self] using herr).eventually (gt_mem_nhds hε)
  filter_upwards [herr', htotal.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w he ht
  dsimp only
  intro M q hM hq
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  intro κ _ α hα hs d hd h hh
  let μ := conditionMass (dyadicPoolTupleMass
    (fun _ : Fin n => (constructedMasterFamily N D hD).pool w (l w))) (primeSampleGood T)
  have hμ : ∀ x, 0 ≤ μ x := conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg _)
  have htμ : total μ = 1 := conditionMass_total _ _ ht
  have hb := finiteMass_good_event_statistic_bound (tensor μ μ)
    (tensor_nonneg _ _ hμ hμ) (by rw [tensor_total, htμ, one_mul])
    (roughPolynomialGoodEvent w f f)
    (fun xy => weightedSubgroupGowersValue
      (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f xy.1).natAbs / M) ⊔
        multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M f xy.2).natAbs / M)) α d h)
    (weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) α d h)
    (weightedSubgroupGowersValue_nonneg _ α hα d hd h)
    (fun _ => weightedSubgroupGowersValue_le_one _ α hα hs d hd h hh) (by
      intro xy hxy
      rw [predictionCubeModulus_quotient_rough w M hM,
        predictionCubeModulus_quotient_rough w M hM,
        coprime_multiple_subgroups_sup (ZMod q) _ _ hxy.2])
  exact hb.trans (add_le_add le_rfl he.le)

end Hindman168
