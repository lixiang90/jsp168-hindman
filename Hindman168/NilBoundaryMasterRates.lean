import Hindman168.MasterPolynomialTranslationGrowth
import Hindman168.NilDivisorBoundary

/-! The larger error from the common-period proof vanishes under the
actual constructed master scales. Gap and root indices may vary with
stage, with only their original order and divisor budget required. -/

namespace Hindman168
open Filter Asymptotics
open FiniteMass
open scoped Topology Classical

theorem powerDominates_ratio_of_polynomial_bound {α : Type*} {l : Filter α}
    {F Q Y : α → ℝ} (h : PowerDominates l F Q) (p : ℕ) (A : ℝ)
    (hY : ∀ᶠ w in l, |Y w| ≤ A * |Q w ^ p|) :
    Tendsto (fun w => Y w / F w) l (𝓝 0) := by
  have ho : Y =O[l] (fun w => Q w ^ p) := IsBigO.of_bound A (by
    simpa only [Real.norm_eq_abs] using hY)
  exact (ho.trans_isLittleO (h p)).tendsto_div_nhds_zero

theorem MasterParameterConditions.nil_boundary_period_ratio_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin N) (K : ℕ → ℕ)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (gap w).val) :
    Tendsto (fun w => ((primorial w * K w : ℕ) : ℝ) / F.gap w (gap w).val) atTop (𝓝 0) := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) gap
  apply powerDominates_ratio_of_polynomial_bound hg 2 1
  filter_upwards [hF.primorial_le_modulus, hK] with w hW hk
  have hw : primorial w ≤ F.auxiliary w (gap w).val := hW.trans (F.modulus_le_auxiliary _ _)
  have hWr : (primorial w : ℝ) ≤ F.auxiliary w (gap w).val := by exact_mod_cast hw
  have hKr : (K w : ℝ) ≤ F.auxiliary w (gap w).val := by exact_mod_cast hk
  have hP := Nat.cast_nonneg (α := ℝ) (F.pool w (gap w).val).upper
  have hA := Nat.cast_nonneg (α := ℝ) (F.auxiliary w (gap w).val)
  have hsq : (0 : ℝ) ≤ ((F.pool w (gap w).val).upper + (F.auxiliary w (gap w).val : ℝ)) ^ 2 := sq_nonneg _
  have hp := mul_le_mul hWr hKr (Nat.cast_nonneg (K w)) hA
  simp only [Nat.cast_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (primorial w : ℝ) * K w), abs_of_nonneg hsq, one_mul]
  nlinarith

theorem MasterParameterConditions.nil_boundary_endpoint_ratio_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) (K : ℕ → ℕ)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (gap w).val) :
    Tendsto (fun w => ((primorial w * K w : ℕ) : ℝ) *
      ((F.gap w (gap w).val : ℝ) + 1) / F.cutoff w (pivot w).val) atTop (𝓝 0) := by
  have hg := powerDominates_log_to_cutoff (hF.indexed_cutoff_gap_growth pivot)
  apply powerDominates_ratio_of_polynomial_bound hg 3 2
  filter_upwards [hF.primorial_le_modulus, hF.auxiliary_le_gap_eventually pivot, horder, hK]
    with w hW haux ho hk
  let G : ℝ := F.gap w (pivot w).val
  have hG : 1 ≤ G := by
    dsimp [G]
    exact_mod_cast (Nat.succ_le_of_lt (hF.gap_positive w (pivot w).val))
  have hWW : primorial w ≤ F.gap w (pivot w).val :=
    hW.trans ((F.modulus_le_auxiliary _ _).trans haux)
  have hKK : K w ≤ F.gap w (pivot w).val :=
    hk.trans ((hF.auxiliary_monotone w ho).trans haux)
  have hLL := hF.gap_monotone w ho
  have hw : (primorial w : ℝ) ≤ G := by dsimp [G]; exact_mod_cast hWW
  have hk' : (K w : ℝ) ≤ G := by dsimp [G]; exact_mod_cast hKK
  have hl : (F.gap w (gap w).val : ℝ) + 1 ≤ 2 * G := by
    have hh : (F.gap w (gap w).val : ℝ) ≤ G := by dsimp [G]; exact_mod_cast hLL
    linarith
  have hq : (primorial w : ℝ) * K w ≤ G ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (K w), Nat.cast_nonneg (α := ℝ) (primorial w)]
  have hp := mul_le_mul hq hl (by positivity : 0 ≤ (F.gap w (gap w).val : ℝ) + 1) (sq_nonneg G)
  have he : G ^ 2 * (2 * G) = 2 * G ^ 3 := by ring
  rw [he] at hp
  dsimp [G] at hp hG
  have hpow : (0 : ℝ) ≤ (F.gap w (pivot w).val : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
  simpa only [Nat.cast_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (primorial w : ℝ) * K w * ((F.gap w (gap w).val : ℝ) + 1)),
    abs_of_nonneg hpow] using hp

theorem MasterParameterConditions.nil_boundary_raw_geometry
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (pivot : ℕ → Fin N) :
    ∀ᶠ w in atTop, 2 ≤ F.cutoff w (pivot w).val ∧
      2 ≤ Real.log (F.cutoff w (pivot w).val : ℝ) ∧
      (primorial w : ℝ) / F.cutoff w (pivot w).val ≤ 1 := by
  have hg := hF.root_gap_sampling_growth pivot 0
    (V := fun w => F.auxiliary w (pivot w).val) (H := fun _ => 0)
    (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => by simp))
  have hlog := (hF.indexed_cutoff_gap_growth pivot).eventually_bound
    (Eventually.of_forall (fun w => nat_log_nonneg _))
    (Eventually.of_forall (fun w => Nat.cast_nonneg _)) 0 (by norm_num : (0 : ℝ) < 2)
  filter_upwards [sampling_eventually_geometry hg, hlog] with w hw hl
  simp only [pow_zero, mul_one] at hl
  have hX : (0 : ℝ) < F.cutoff w (pivot w).val := by exact_mod_cast (by omega : 0 < F.cutoff w (pivot w).val)
  refine ⟨by omega, hl, ?_⟩
  apply (div_le_iff₀ hX).mpr
  have hW : (primorial w : ℝ) ≤ F.cutoff w (pivot w).val := by
    exact_mod_cast (by omega : primorial w ≤ F.cutoff w (pivot w).val)
  simpa only [one_mul] using hW

noncomputable def nilBoundaryMasterError {N : ℕ} (F : MasterParameterFamily)
    (gap pivot : ℕ → Fin N) (K : ℕ → ℕ) (d w : ℕ) : ℝ :=
  (4 + 8 * (d : ℝ)) * (primorial w * K w : ℕ) / F.gap w (gap w).val +
    (primorial w * K w : ℕ) * ((F.gap w (gap w).val : ℝ) + 1) / F.cutoff w (pivot w).val

theorem MasterParameterConditions.nil_boundary_error_tendsto
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) (K : ℕ → ℕ) (d : ℕ)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (gap w).val) :
    Tendsto (nilBoundaryMasterError F gap pivot K d) atTop (𝓝 0) := by
  have h1 := (hF.nil_boundary_period_ratio_tendsto gap K hK).const_mul (4 + 8 * (d : ℝ))
  have h2 := hF.nil_boundary_endpoint_ratio_tendsto gap pivot K horder hK
  change Tendsto (fun w => (4 + 8 * (d : ℝ)) * (primorial w * K w : ℕ) / F.gap w (gap w).val +
    (primorial w * K w : ℕ) * ((F.gap w (gap w).val : ℝ) + 1) / F.cutoff w (pivot w).val) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero, zero_add] using h1.add h2

theorem MasterParameterConditions.nil_boundary_uniform_divisor_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap pivot : ℕ → Fin N) (K : ℕ → ℕ) (d J : ℕ)
    (hJ : 0 < J) (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (gap w).val) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ σ : ℕ,
      0 < σ → σ ≤ K w → (primorial w).Coprime σ →
      expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
        (divisorBoundaryTest σ (F.gap w (gap w).val)
          (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w))) ≤
        4 * (d : ℝ) / J + ε := by
  intro ε hε
  have he := (hF.nil_boundary_error_tendsto gap pivot K d horder hK).eventually
    (gt_mem_nhds hε)
  filter_upwards [hF.nil_boundary_raw_geometry pivot, he] with w hw herr
  intro σ hp hk hc
  have hb := integerMass_divisorBoundary_uniform_bound hw.1 (primorial_pos w) hp hk
    (hF.gap_positive w (gap w).val) hJ hc
    (zeroPrimeCubeMargin_scale_bound d (F.gap w (gap w).val) J (F.modulus w)) hw.2.1 hw.2.2
  have hb' : expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
      (divisorBoundaryTest σ (F.gap w (gap w).val)
        (zeroPrimeCubeMargin d (F.gap w (gap w).val) J (F.modulus w))) ≤
      4 * (d : ℝ) / J + nilBoundaryMasterError F gap pivot K d w := by
    simpa only [nilBoundaryMasterError, add_assoc] using hb
  linarith

end Hindman168
