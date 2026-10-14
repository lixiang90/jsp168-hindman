import Hindman168.AlignmentDyadicResidueGrowth
import Hindman168.AlignmentDyadicExposureGeometry

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_dyadic_residue_ratio_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F) (C : ℝ) :
    ∀ᶠ w in atTop, ∀ j : Fin n, ∀ x : ℕ, F.cutoff w j.val ≤ x →
      C ≤ ((2 ^ Nat.log2 x : ℕ) : ℝ) /
        (((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) : ℝ) := by
  have hh : ∀ᶠ w in atTop, ∀ j : Fin n, ∀ x : ℕ, F.cutoff w j.val ≤ x →
      (max C 1) * (((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) : ℝ) ≤
        ((2 ^ Nat.log2 x : ℕ) : ℝ) :=
    Filter.eventually_all.mpr (fun j => alignment_dyadic_residue_eventually_large hF
      j.val (max C 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  filter_upwards [hh] with w hw j x hx
  have hL : (0 : ℝ) < (((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (F.modulus w).pos (Nat.pow_pos (primorial_pos w))
  exact (le_max_left C 1).trans ((le_div_iff₀ hL).mpr (hw j x hx))

theorem alignment_dyadic_residue_ratio_tendsto
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (j : ℕ → Fin n) (x : ℕ → ℕ)
    (hx : ∀ᶠ w in atTop, F.cutoff w (j w).val ≤ x w) :
    Tendsto (fun w => ((2 ^ Nat.log2 (x w) : ℕ) : ℝ) /
      (((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  filter_upwards [alignment_dyadic_residue_ratio_eventually hF C, hx] with w hw hxw
  exact hw (j w) (x w) hxw

theorem alignment_exposed_dyadic_ratio_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (C : ℝ) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ,
      alignmentShortExposureDyadicGood F w T (alignmentShortExposureKey F w i T x) →
      ∀ j ∈ T, C ≤ ((2 ^ Nat.log2 (x j) : ℕ) : ℝ) /
        (((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) : ℝ) := by
  filter_upwards [alignment_dyadic_residue_ratio_eventually hF C] with w hw x hx j hj
  have hg := (alignmentShortExposureDyadicGood_key F w i T x).mp hx j hj
  have hpos : 0 < x j := by
    by_contra hn
    have hz : x j = 0 := by omega
    have hc := hF.cutoff_positive w j.val
    have hh := hg.2
    have hl := hg.1
    simp only [hz, Nat.log2_zero, pow_zero] at hl hh
    have : F.cutoff w j.val = 1 := by omega
    simp only [this] at hh
    norm_num at hh
  exact hw j (x j) (hg.1.trans (Nat.log2_self_le hpos.ne'))

end Hindman168
