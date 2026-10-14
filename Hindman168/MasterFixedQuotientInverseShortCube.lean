import Hindman168.MasterInverseShortCubeEstimate

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- A prescribed positive quotient scale has an explicit wrapping cost.
The positive global threshold is selected before all master data. -/
theorem master_shortCube_fixed_quotient_global_threshold (d J : ℕ) (hJ : 0 < J)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0)
        (pol : MvPolynomial (Fin n) ℤ) (_hpol : pol ∈ D)
        (T : Finset (MvPolynomial (Fin n) ℤ)) (_hT : ∀ p ∈ T, p ≠ 0) (_hpolT : pol ∈ T)
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
            (F.gap w (gap w).val) (F.cutoff w (pivot w).val) d J pol f x|) <
              ε + 4 * (d : ℝ) / J := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hc : 0 < (2 * (J : ℝ)) ^ d := by positivity
  let η := ε / (2 * (2 * (J : ℝ)) ^ d)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hc)
  have hscale : (2 * (J : ℝ)) ^ d * η = ε / 2 := by
    dsimp only [η]
    field_simp [ne_of_gt hc]
  obtain ⟨δ, hδ, hb⟩ := finiteWeightedBesselModulus_uniform_small (2 ^ d) (by positivity) η hη
  let θ := δ / 2
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hmod : finiteWeightedBesselModulus (2 ^ d) (2 * θ) < η := by
    apply hb
    dsimp only [θ]
    linarith
  refine ⟨θ, hθ, ?_⟩
  intro n N D hD pol hpol T hT hpolT gap pivot horder
  have he := constructedMasterFamily_shortCube_budget_of_modulus_eventually D hD pol hpol
    T hT hpolT gap pivot horder d J hJ θ η (ε / 2) hθ (by positivity) hmod
  filter_upwards [he] with w hw
  dsimp only
  intro f hf hg
  have hx := hw f hf hg
  rw [hscale] at hx
  linarith

/-- Conditional on the interval inverse existence input, a prescribed J
has a positive projection threshold independent of N and arithmetic data.
The original integer statistic retains the explicit 4*d/J cost. -/
theorem master_inverse_shortCube_fixed_quotient_threshold (s d J : ℕ) (hJ : 0 < J)
    (hinverse : HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0)
        (pol : MvPolynomial (Fin n) ℤ) (_hpol : pol ∈ D)
        (T : Finset (MvPolynomial (Fin n) ℤ)) (_hT : ∀ p ∈ T, p ≠ 0) (_hpolT : pol ∈ T)
        (gap pivot : ℕ → Fin N) (_horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val),
      let F := constructedMasterFamily N D hD
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (h : boundedHilbertFamilies (fun w =>
          FiniteMassL2 (integerMass (F.cutoff w (pivot w).val) (primorial w))))
        (_hf : ∀ w y, |h.val w y| ≤ 1),
      ‖(nativeNilHilbertSubspace.{u} s F
        (fun w => integerMass (F.cutoff w (pivot w).val) (primorial w)) U gap).starProjection
          (hilbertFamilyToCompletion _ U h)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        let μ := conditionMass (dyadicPoolTupleMass
          (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
        expectation μ (fun x => |integerPredictionShortCubeStatistic w (F.modulus w : ℕ)
          (F.gap w (gap w).val) (F.cutoff w (pivot w).val) d J pol (fun y => h.val w y) x|) <
            ε + 4 * (d : ℝ) / J := by
  obtain ⟨θ, hθ, hshort⟩ := master_shortCube_fixed_quotient_global_threshold d J hJ ε hε
  have hk : (0 : ℕ) < 2 ^ d := by positivity
  have ht : (0 : ℕ) < 2 ^ d + 2 ^ d - 1 := by omega
  obtain ⟨κ, hκ, hproject⟩ := native_interval_inverse_uniform_projection_threshold
    s (2 ^ d + 2 ^ d - 1) ht hinverse θ hθ
  refine ⟨κ, hκ, ?_⟩
  intro n N D hD pol hpol T hT hpolT gap pivot horder F U hU h hf hp
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  have hnorm := hproject hF U hU gap pivot horder h hf hp
  have hstat := hshort D hD pol hpol T hT hpolT gap pivot horder
  filter_upwards [hU hstat, hnorm] with w hw hn
  letI : NeZero (F.gap w (gap w).val / (F.modulus w : ℕ)) :=
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  exact hw (fun y => h.val w y) (hf w) hn.le

end Hindman168
