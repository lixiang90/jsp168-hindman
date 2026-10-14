import Hindman168.MasterFixedBesselModulus
import Hindman168.MasterShortCubeBesselBudget

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

theorem constructedMasterFamily_shortCube_budget_of_modulus_eventually
    {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (pol : MvPolynomial (Fin n) ℤ) (hpol : pol ∈ D)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (hT : ∀ f ∈ T, f ≠ 0) (hpolT : pol ∈ T)
    (gap pivot : ℕ → Fin N) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (d J : ℕ) (hJ : 0 < J) (θ η ξ : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ)
    (hmod : finiteWeightedBesselModulus (2 ^ d) (2 * θ) < η) :
    let F := constructedMasterFamily N D hD
    let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
    ∀ᶠ w in atTop,
      let X := F.cutoff w (pivot w).val
      let M := (F.modulus w : ℕ)
      let R := F.gap w (gap w).val
      let q := R / M
      letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
      let μ := conditionMass (dyadicPoolTupleMass
        (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
      ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      masterCompleteGlobalGowersValue F gap pivot w (2 ^ d + 2 ^ d - 1) f ≤ θ →
        expectation μ (fun x => |integerPredictionShortCubeStatistic w M R X d J pol f x|) <
          (2 * (J : ℝ)) ^ d * η + 4 * (d : ℝ) / J + ξ := by
  let F := constructedMasterFamily N D hD
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  have hb := constructedMasterFamily_canonical_cell_bessel_of_modulus_eventually D hD
    pol (hD pol hpol) T hT gap pivot horder (2 ^ d) (by positivity) θ η hθ hmod
  have hshort := hF.common_cyclic_shortCube_gowers_eventually gap pivot horder pol hpol d J hJ ξ hξ
  have htotal := constructedMasterFamily_primeGoodSample_tendsto_one N D hD T hT
    (fun w => (gap w).val)
  filter_upwards [hb, hshort, hF.canonical_cell_probability_eq_aligned_eventually gap pivot,
    htotal.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w hw hs hm ht
  dsimp only
  let X := F.cutoff w (pivot w).val
  let M := (F.modulus w : ℕ)
  let R := F.gap w (gap w).val
  let q := R / M
  letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  let μ := conditionMass (dyadicPoolTupleMass
    (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
  intro f hf hg
  let v := fun x => weightedSubgroupGowersValue
    (multipleAddSubgroup (ZMod q) ((predictionCubeModulus w M pol x).natAbs / M))
    (masterCompleteCellProbability F gap pivot w) (2 ^ d) (fun c z =>
      f (c.val.1 * (M * q : ℕ) + c.val.2.val + (M : ℤ) * z.val))
  let z := fun x => |integerPredictionShortCubeStatistic w M R X d J pol f x|
  have hv : expectation μ v < η := hw f hf hg
  have hμ : ∀ x, 0 ≤ μ x := conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg _)
  have htμ : total μ = 1 := conditionMass_total _ _ ht
  have he : M * q = R := Nat.mul_div_cancel' (hF.gap_modulus_dvd w (gap w).val)
  have hz (x : Fin n → ℕ) (hx : x ∈ μ.support) :
      z x ≤ (2 * (J : ℝ)) ^ d * v x + 4 * (d : ℝ) / J + ξ := by
    obtain ⟨hxp, hgood⟩ := conditioned_dyadic_tuple_support (F.pool w (gap w).val) T x hx
    have hpx := hs x hxp (hgood.2 pol hpolT) f hf
    have hinst : Fintype.ofFinite (multipleAddSubgroup (ZMod q)
        ((predictionCubeModulus w M pol x).natAbs / M)) =
        (inferInstance : Fintype (multipleAddSubgroup (ZMod q)
          ((predictionCubeModulus w M pol x).natAbs / M))) := Subsingleton.elim _ _
    rw [hinst] at hpx
    dsimp only [z, v]
    rw [he, hm]
    exact hpx
  have hmean := expectation_mono_support μ z
    (fun x => (2 * (J : ℝ)) ^ d * v x + 4 * (d : ℝ) / J + ξ) hμ hz
  have hc : 0 < (2 * (J : ℝ)) ^ d := by positivity
  calc
    _ ≤ (2 * (J : ℝ)) ^ d * expectation μ v + 4 * (d : ℝ) / J + ξ := by
      simpa only [expectation_add, expectation_const_mul, expectation_const, htμ, one_mul] using hmean
    _ < _ := by linarith [mul_lt_mul_of_pos_left hv hc]

/-- J and the global norm threshold are fixed from d and the requested
error before choosing N, polynomial data, original cell laws or gaps. -/
theorem master_shortCube_uniform_global_threshold (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ θ : ℝ, 0 < θ ∧
      ∀ {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
        (pol : MvPolynomial (Fin n) ℤ) (_hpol : pol ∈ D)
        (T : Finset (MvPolynomial (Fin n) ℤ)) (_hT : ∀ f ∈ T, f ≠ 0) (_hpolT : pol ∈ T)
        (gap pivot : ℕ → Fin N) (_horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val),
      let F := constructedMasterFamily N D hD
      let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
      ∀ᶠ w in atTop,
        let q := F.gap w (gap w).val / (F.modulus w : ℕ)
        letI : NeZero q := ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
        let μ := conditionMass (dyadicPoolTupleMass
          (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
        ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
        masterCompleteGlobalGowersValue F gap pivot w (2 ^ d + 2 ^ d - 1) f ≤ θ →
          expectation μ (fun x => |integerPredictionShortCubeStatistic w (F.modulus w : ℕ)
            (F.gap w (gap w).val) (F.cutoff w (pivot w).val) d J pol f x|) < ε := by
  obtain ⟨J, hlarge⟩ := exists_nat_gt (16 * ((d : ℝ) + 1) / ε)
  have hJR : (0 : ℝ) < J := (div_pos (by positivity) hε).trans hlarge
  have hJ : 0 < J := by exact_mod_cast hJR
  have hcost : 4 * (d : ℝ) / J < ε / 4 := by
    apply (div_lt_iff₀ hJR).mpr
    have hh := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  have hc : 0 < (2 * (J : ℝ)) ^ d := by positivity
  let η := ε / (4 * (2 * (J : ℝ)) ^ d)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hc)
  have hscale : (2 * (J : ℝ)) ^ d * η = ε / 4 := by
    dsimp only [η]
    field_simp [ne_of_gt hc]
  obtain ⟨δ, hδ, hb⟩ := finiteWeightedBesselModulus_uniform_small (2 ^ d) (by positivity) η hη
  let θ := δ / 2
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hmod : finiteWeightedBesselModulus (2 ^ d) (2 * θ) < η := by
    apply hb
    dsimp only [θ]
    linarith
  refine ⟨J, hJ, θ, hθ, ?_⟩
  intro n N D hD pol hpol T hT hpolT gap pivot horder
  have he := constructedMasterFamily_shortCube_budget_of_modulus_eventually D hD pol hpol
    T hT hpolT gap pivot horder d J hJ θ η (ε / 4) hθ (by positivity) hmod
  filter_upwards [he] with w hw
  dsimp only
  intro f hf hg
  exact (hw f hf hg).trans (by rw [hscale]; linarith)

end Hindman168
