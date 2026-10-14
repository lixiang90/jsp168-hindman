import Hindman168.NilAveragedBoundary
import Hindman168.NilBoundaryMasterRates
import Hindman168.MasterTailGapBudgets
import Hindman168.MasterChainSampling

/-! The original (1+ν_B)-weighted bad-root expectation is O_d(1/J)+o(1).
The period and endpoint errors are proved to vanish at the actual master
scales, uniformly in the original tail-divisor draws and varying chains. -/

namespace Hindman168
open Filter
open FiniteMass
open scoped Topology Classical

theorem MasterParameterConditions.nil_boundary_onePlus_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) (K : ℕ → ℕ)
    (ρ : ℕ → Mass ℕ) (d J : ℕ) (hJ : 0 < J)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (gap w).val)
    (hK1 : ∀ᶠ w in atTop, 1 ≤ K w)
    (hρ : ∀ᶠ w in atTop, (∀ σ, 0 ≤ ρ w σ) ∧ total (ρ w) = 1 ∧
      ∀ σ ∈ (ρ w).support, 0 < σ ∧ σ ≤ K w ∧ (primorial w).Coprime σ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
        (fun y => if ¬ intervalInteriorRoot (F.gap w (gap w).val)
          (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w)) y then
          1 + integerDivisorMask (ρ w) y else 0) ≤ 8 * (d : ℝ) / J + ε := by
  intro ε hε
  have he := (hF.nil_boundary_error_tendsto gap pivot K d horder hK).eventually
    (gt_mem_nhds (by positivity : 0 < ε / 2))
  filter_upwards [hF.nil_boundary_raw_geometry pivot, he, hρ, hK1] with w hw herr hρw hkw
  have hb := integerMass_onePlusDivisor_boundary_bound (ρ w) hρw.1 hρw.2.1 hρw.2.2 hkw
    hw.1 (primorial_pos w) (hF.gap_positive w (gap w).val) hJ
    (zeroPrimeCubeMargin_scale_bound d (F.gap w (gap w).val) J (F.modulus w)) hw.2.1 hw.2.2
  have hb' : expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
      (fun y => if ¬ intervalInteriorRoot (F.gap w (gap w).val)
        (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w)) y then
        1 + integerDivisorMask (ρ w) y else 0) ≤
      8 * (d : ℝ) / J + 2 * nilBoundaryMasterError F gap pivot K d w := hb
  linarith

theorem MasterParameterConditions.nil_boundary_chain_eventually
    {n N m : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (i : Fin m)
    (gap : ℕ → Fin N) (d J : ℕ) (hJ : 0 < J)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot i)
    (htail : ∀ᶠ w in atTop, (C w).tail i ⊆ Finset.range (gap w).val) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      expectation (integerMass (F.cutoff w ((C w).pivot i)) (primorial w))
        (fun y => if ¬ intervalInteriorRoot (F.gap w (gap w).val)
          (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w)) y then
          1 + integerDivisorMask (tailMass (primorial w)
            ((C w).tailCutoffs (F.cutoff w) i)) y else 0) ≤ 8 * (d : ℝ) / J + ε := by
  let pivot := fun w => (C w).pivotIndex (hN w) i
  let K := fun w => F.auxiliary w (gap w).val
  apply hF.nil_boundary_onePlus_eventually gap pivot K _ d J hJ horder
    (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun w => by
      dsimp [K]
      have h := F.auxiliary_ge_two w (gap w).val
      omega))
  filter_upwards [hF.raw_cutoffs_valid, htail] with w hw ht
  have hv := chain_tailCutoffs_valid (C w) (F.cutoff w) (primorial w) (hN w)
    (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) i
  refine ⟨tailMass_nonneg (primorial_pos w) _ hv, tailMass_total (primorial_pos w) _ hv, ?_⟩
  intro σ hσ
  obtain ⟨hp, hk, hc⟩ := tailMass_support _ hv σ hσ
  exact ⟨hp, hk.trans (hF.chain_tail_budget_at_gap (C w) w i (gap w).val ht), hc⟩

theorem nil_boundary_choose_scale (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ 8 * (d : ℝ) / J < ε / 2 := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (16 * (d : ℝ) / ε)
  refine ⟨J + 1, Nat.succ_pos _, ?_⟩
  have hJR : (0 : ℝ) < (J + 1 : ℕ) := by positivity
  have hh : 16 * (d : ℝ) / ε < (J + 1 : ℕ) := by exact_mod_cast (by linarith : 16 * (d : ℝ) / ε < (J : ℝ) + 1)
  have hm := (div_lt_iff₀ hε).mp hh
  apply (div_lt_iff₀ hJR).mpr
  nlinarith

theorem MasterParameterConditions.nil_boundary_chain_small
    {n N m : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (i : Fin m)
    (gap : ℕ → Fin N) (d : ℕ)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot i)
    (htail : ∀ᶠ w in atTop, (C w).tail i ⊆ Finset.range (gap w).val) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 0 < J ∧ ∀ᶠ w in atTop,
      expectation (integerMass (F.cutoff w ((C w).pivot i)) (primorial w))
        (fun y => if ¬ intervalInteriorRoot (F.gap w (gap w).val)
          (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w)) y then
          1 + integerDivisorMask (tailMass (primorial w)
            ((C w).tailCutoffs (F.cutoff w) i)) y else 0) < ε := by
  intro ε hε
  obtain ⟨J, hJ, hmain⟩ := nil_boundary_choose_scale d hε
  refine ⟨J, hJ, ?_⟩
  filter_upwards [hF.nil_boundary_chain_eventually C hN i gap d J hJ horder htail
    (ε / 2) (by positivity)] with w hw
  linarith

end Hindman168
