import Hindman168.NilBoundaryOriginalLimit
import Hindman168.MasterDualWeightedLaw

/-! The original master scales supply positive zero-prime shift windows,
uniform original weighted totals and boundary deletion for varying labels. -/

namespace Hindman168
open Filter
open FiniteMass
open scoped Topology Classical

theorem MasterParameterConditions.nil_shift_window_eventually_positive
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin N) (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ w in atTop, 0 < F.gap w (gap w).val / (J * (F.modulus w : ℕ)) := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) gap
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  filter_upwards [hg.eventually_bound (A := (J : ℝ))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => by positivity)) 1 hJR] with w hw
  simp only [pow_one] at hw
  have hM : (F.modulus w : ℕ) ≤ (F.pool w (gap w).val).upper + F.auxiliary w (gap w).val :=
    (F.modulus_le_auxiliary _ _).trans (Nat.le_add_left _ _)
  have hMR : ((F.modulus w : ℕ) : ℝ) ≤ (F.pool w (gap w).val).upper +
      (F.auxiliary w (gap w).val : ℝ) := by exact_mod_cast hM
  have hc : J * (F.modulus w : ℕ) ≤ F.gap w (gap w).val := by
    have hm := (mul_le_mul_of_nonneg_left hMR hJR.le).trans hw
    exact_mod_cast hm
  exact Nat.div_pos hc (Nat.mul_pos hJ (F.modulus w).pos)

theorem MasterParameterConditions.nil_boundary_label_eventually
    {n N m : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin m)
    (gap : ℕ → Fin N) (d J : ℕ) (hJ : 0 < J)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => if ¬ intervalInteriorRoot (F.gap w (gap w).val)
          (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w)) y then
          1 + masterPredictionBlockMask F C label w y else 0) ≤ 8 * (d : ℝ) / J + ε := by
  let pivot := fun w => (C w).pivotIndex (hN w) (label w)
  let K := fun w => F.auxiliary w (gap w).val
  apply hF.nil_boundary_onePlus_eventually gap pivot K _ d J hJ horder
    (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun w => by
      dsimp [K]
      have h := F.auxiliary_ge_two w (gap w).val
      omega))
  filter_upwards [hF.raw_cutoffs_valid, htail] with w hw ht
  have hv := chain_tailCutoffs_valid (C w) (F.cutoff w) (primorial w) (hN w)
    (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) (label w)
  refine ⟨tailMass_nonneg (primorial_pos w) _ hv, tailMass_total (primorial_pos w) _ hv, ?_⟩
  intro σ hσ
  obtain ⟨hp, hk, hc⟩ := tailMass_support _ hv σ hσ
  exact ⟨hp, hk.trans (hF.chain_tail_budget_at_gap (C w) w (label w) (gap w).val ht), hc⟩

theorem MasterParameterConditions.nil_boundary_label_small
    {n N m : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin m)
    (gap : ℕ → Fin N) (d : ℕ)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 0 < J ∧ ∀ᶠ w in atTop,
      expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => if ¬ intervalInteriorRoot (F.gap w (gap w).val)
          (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w)) y then
          1 + masterPredictionBlockMask F C label w y else 0) < ε := by
  intro ε hε
  obtain ⟨J, hJ, hm⟩ := nil_boundary_choose_scale d hε
  refine ⟨J, hJ, ?_⟩
  filter_upwards [hF.nil_boundary_label_eventually C hN label gap d J hJ horder htail
    (ε / 2) (by positivity)] with w hw
  linarith

theorem MasterParameterConditions.nil_testing_weight_eventually_le
    {n N m : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin m)
    (gap : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val) :
    ∀ᶠ w in atTop, expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
      (fun y => 1 + masterPredictionBlockMask F C label w y) ≤ 3 := by
  let root := fun w => (C w).pivotIndex (hN w) (label w)
  exact hF.dual_weighted_root_mass_eventually_le C hN label
    (fun w => Finset.range (gap w).val) htail root
    (horder.mono (fun _ hw => Finset.range_mono hw))

end Hindman168
