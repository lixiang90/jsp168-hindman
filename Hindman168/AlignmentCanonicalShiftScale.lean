import Hindman168.AlignmentExposedArrayOffsets
import Hindman168.AlignmentNumericalPolynomialBounds
import Hindman168.AlignmentCubeStepRatio

namespace Hindman168
open Filter
open scoped Topology BigOperators

theorem alignmentPairProgression_eventually_dvd
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ d : ℕ) (hq : 0 < q₀) (hd : 0 < d) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j, Nat.Coprime (x j) (primorial w)) →
      ∀ i : Fin n, ∀ e : AlignmentAddingPair n i,
        (d : ℤ) ∣ alignmentPairProgression q₀ w (F.modulus w) e x := by
  filter_upwards [eventually_ge_atTop (q₀ + 1), fixed_integer_eventually_dvd_primorial_power hd.ne']
    with w hw hdiv x hx i e
  have h := alignmentPairResidue_master_data hF hq hw x hx e
  have hdZ : (d : ℤ) ∣ (primorial w : ℤ) ^ w := by exact_mod_cast hdiv
  exact hdZ.trans h.2.2.2.2.1

theorem alignmentPairProgression_scale_small
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ : ℕ) (hq : 0 < q₀) (i : Fin n) (T : Finset (Fin n))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j, Nat.Coprime (x j) (primorial w)) →
      (∀ j, j < i → x j ≤ F.cutoff w j.val ^ 2) →
      ∀ e : AlignmentAddingPair n i,
        |(alignmentPairProgression q₀ w (F.modulus w) e x : ℝ)| ≤ eps * alignmentCubeScale F w i T x := by
  filter_upwards [eventually_ge_atTop (q₀ + 1),
    master_microcell_eventually_polynomial_small hF (fun _ => i) 3 2 heps]
    with w hw hg x hx hcut e
  have hd := alignmentPairResidue_master_data hF hq hw x hx e
  have hb := alignmentProgressionShift_polynomial_bound hF q₀ w x hcut e
    (alignmentPairResidue q₀ w (F.modulus w) e x) hd.2.1.le
    (alignmentPairProgression q₀ w (F.modulus w) e x)
    (alignmentPairProgression_exact hF hq hw x hx e)
  have hbR : |(F.modulus w : ℝ) * (alignmentPairProgression q₀ w (F.modulus w) e x : ℝ)| ≤
      2 * (F.auxiliary w i.val : ℝ) ^ 3 := by exact_mod_cast hb
  have hM : (0 : ℝ) < F.modulus w := by exact_mod_cast (F.modulus w).pos
  rw [abs_mul, abs_of_pos hM] at hbR
  have ha : (1 : ℝ) ≤ (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by
    have hp : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by positivity
    exact_mod_cast hp
  have hR : (0 : ℝ) ≤ alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by positivity
  unfold alignmentCubeScale alignmentShortBinVolume
  rw [Nat.cast_mul, ← mul_div_assoc]
  apply (le_div_iff₀ hM).mpr
  have hh := mul_le_mul_of_nonneg_right ha hR
  have hh' := mul_le_mul_of_nonneg_left hh heps.le
  nlinarith

end Hindman168
