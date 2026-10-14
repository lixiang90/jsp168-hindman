import Hindman168.AlignmentCanonicalShiftScale
import Hindman168.AlignmentSingleCoordinateTranslation
import Hindman168.AlignmentRetainedBoxGeometry

namespace Hindman168
open Filter
open scoped Topology Classical

theorem alignment_canonical_face_counting_eventually
    {ι : Type*} [Fintype ι] {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ d : ℕ) (hq : 0 < q₀) (hd : 0 < d) (i : Fin n) (T : Finset (Fin n))
    (c K eps : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j, Nat.Coprime (x j) (primorial w)) →
      (∀ j, j < i → x j ≤ F.cutoff w j.val ^ 2) →
      ∀ e : AlignmentAddingPair n i, ∀ a : ι, ∀ L U r : ι → ℤ,
      (∀ j, c * alignmentCubeScale F w i T x ≤ (U j : ℝ) - L j) →
      ∀ f : (ι → ℤ) → ℂ, (∀ z, ‖f z‖ ≤ K) →
      ‖finiteComplexSetMean (alignmentBoxClass L U r d)
          (fun z => f (fun j => z j + if j = a then alignmentPairProgression q₀ w (F.modulus w) e x else 0)) -
        finiteComplexSetMean (alignmentBoxClass L U r d) f‖ ≤ eps := by
  have hden : 0 < 4 * (K + 1) := by positivity
  filter_upwards [alignmentPairProgression_eventually_dvd hF q₀ d hq hd,
    alignmentPairProgression_scale_small hF q₀ hq i T (eps := eps * c / (4 * (K + 1))) (by positivity),
    alignment_retained_step_small_eventually hF i T d hd (eps := c / 2) (by positivity)]
    with w hdiv hsmall hstep x hx hcut e a L U r hlen f hf
  have haux : 1 ≤ F.auxiliary w i.val := (by omega : 1 ≤ 2).trans (F.auxiliary_ge_two w i.val)
  have hs := hstep x 1 zero_lt_one haux
  simp only [Nat.cast_one, mul_one] at hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hz : 0 < c * alignmentCubeScale F w i T x := by nlinarith
  have hb := alignment_single_coordinate_translation_scale_bound L U r a
    (alignmentPairProgression q₀ w (F.modulus w) e x) d (by exact_mod_cast hd)
    (hdiv x hx i e) (alignmentCubeScale F w i T x) c hz
    (by simp only [Int.cast_natCast]; nlinarith) hlen f K hK hf
  apply hb.trans
  apply (div_le_iff₀ hz).mpr
  have hdelta := hsmall x hx hcut e
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at hdelta
  nlinarith [abs_nonneg (alignmentPairProgression q₀ w (F.modulus w) e x : ℝ)]

end Hindman168
