import Hindman168.PredictionInsertionAsymptotics
import Hindman168.FiniteMasterSelection

/-!
# Actual master scales control root displacement

Earlier gaps are at most the selected root gap by their divisibility.
The raw cutoff at that root dominates all powers of a fixed multiple of
its gap together with primorial and the original auxiliary budget. This
supplies the harmonic insertion growth hypothesis from master conditions.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.gap_monotone {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w : ℕ) : Monotone (F.gap w) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact Nat.le_of_dvd (hF.gap_positive w j) (hF.gap_earlier_dvd w i j hij)
  · exact le_rfl

theorem MasterParameterConditions.primorial_dvd_modulus {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) :
    ∀ᶠ w in atTop, primorial w ∣ (F.modulus w : ℕ) := by
  filter_upwards [eventually_ge_atTop 1] with w hw
  have hd : primorial w ∣ (primorial w) ^ w := by
    simpa only [pow_one] using pow_dvd_pow (primorial w) hw
  exact hd.trans (hF.primorial_power_dvd w)

theorem MasterParameterConditions.indexed_cutoff_gap_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w (index w).val : ℝ))
      (fun w => (F.gap w (index w).val : ℝ)) :=
  PowerDominates.finite_choice (fun i : Fin N => hF.cutoff_growth i.val) index

theorem MasterParameterConditions.auxiliary_le_gap_eventually {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) :
    ∀ᶠ w in atTop, F.auxiliary w (index w).val ≤ F.gap w (index w).val := by
  have hg (i : Fin N) := (hF.gap_growth i.val).eventually_bound
    (Eventually.of_forall (fun w => (Nat.cast_nonneg (F.gap w i.val) : (0 : ℝ) ≤ F.gap w i.val)))
    (Eventually.of_forall (fun w => (by positivity : (0 : ℝ) ≤
      (F.pool w i.val).upper + F.auxiliary w i.val))) 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_all.mpr hg] with w hw
  have hh := hw (index w)
  simp only [pow_one, one_mul] at hh
  have hb : (F.auxiliary w (index w).val : ℝ) ≤ F.gap w (index w).val := by
    linarith [(Nat.cast_nonneg (F.pool w (index w).val).upper : (0 : ℝ) ≤ (F.pool w (index w).val).upper)]
  exact_mod_cast hb

theorem MasterParameterConditions.root_gap_sampling_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N)
    (C : ℕ) {V H : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (index w).val)
    (hH : ∀ᶠ w in atTop, H w ≤ C * F.gap w (index w).val) :
    PowerDominates atTop (fun w => (F.cutoff w (index w).val : ℝ))
      (fun w => (samplingSize (primorial w) 0 (H w) (V w) : ℝ)) := by
  have hg := hF.indexed_cutoff_gap_growth index
  have hgaplarge : ∀ᶠ w in atTop, C + 4 ≤ F.gap w (index w).val := by
    have hh := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) index
    filter_upwards [hh.eventually_bound (A := ((C + 4 : ℕ) : ℝ))
      (Eventually.of_forall (fun w => Nat.cast_nonneg (F.gap w (index w).val)))
      (Eventually.of_forall (fun w => by positivity))
      0 (by exact_mod_cast (by omega : 0 < C + 4))] with w hw
    simp only [pow_zero, mul_one] at hw
    exact_mod_cast hw
  apply (powerDominates_log_to_cutoff hg).mono_base 2
  filter_upwards [hF.primorial_le_modulus, hF.auxiliary_le_gap_eventually index,
    hgaplarge, hV, hH] with w hWw haw hgw hVw hHw
  have hW : primorial w ≤ F.gap w (index w).val :=
    hWw.trans ((F.modulus_le_auxiliary _ _).trans haw)
  have hv : V w ≤ F.gap w (index w).val := hVw.trans haw
  have hs : samplingSize (primorial w) 0 (H w) (V w) ≤
      (F.gap w (index w).val) ^ 2 := by
    unfold samplingSize
    nlinarith
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, by exact_mod_cast hs⟩

theorem predictionRootDisplacementCap_le_common_gap {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (R : Fin b → ℕ) (Rmax : ℕ)
    (hR : ∀ q, R q ≤ Rmax) :
    predictionRootDisplacementCap dir R ≤
      (∑ i, (cubeRootDirection (dir i).2.val).natAbs) * Rmax := by
  unfold predictionRootDisplacementCap
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hR (dir i).1))

end Hindman168
