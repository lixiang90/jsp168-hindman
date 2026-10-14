import Hindman168.SelectedAlignmentNativeWindow
import Hindman168.AlignmentCanonicalShiftScale

/-! Actual ambient adding pairs whose source pivot precedes the model gap
have uniformly small shifts at that gap. The ambient scale dimension and
principal target pivot are unchanged. -/
namespace Hindman168
open Filter
open scoped Topology BigOperators Classical

theorem selected_alignmentIntegerNumerator_polynomial_bound
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) {i : Fin n} (gap : Fin n) (t : Fin n → ℕ)
    (ht : ∀ j, j < gap → t j ≤ F.cutoff w j.val ^ 2) (e : AlignmentAddingPair n i) (he : e.sourcePivot < gap) :
    alignmentIntegerNumerator q₀ w e t ≤ F.auxiliary w gap.val ^ 2 := by
  have hs : alignmentIntegerScale w (alignmentPairSourceBlock e) ≤ (F.modulus w : ℕ) :=
    hF.subset_scale_le w _ (alignmentNaturalBlock_subset _)
  have hp := alignment_earlier_block_product_bound hF w gap t ht _ (by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact he
    · obtain ⟨c,hc⟩ := e.target_nonempty
      exact (e.source_before_target j hj c hc).trans ((e.target_before_sourcePivot c hc).trans he))
  unfold alignmentIntegerNumerator
  have hd := (Nat.div_le_self (alignmentIntegerScale w (alignmentPairSourceBlock e))
    (q₀ * alignmentIntegerScale w (alignmentPairTargetBlock e))).trans hs
  have hm := Nat.mul_le_mul hd hp
  exact hm.trans (by simpa only [pow_two] using
    Nat.mul_le_mul_right (F.auxiliary w gap.val) (F.modulus_le_auxiliary w gap.val))

theorem selected_alignmentProgressionShift_polynomial_bound
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) {i : Fin n} (gap : Fin n) (t : Fin n → ℕ)
    (ht : ∀ j, j < gap → t j ≤ F.cutoff w j.val ^ 2) (e : AlignmentAddingPair n i) (he : e.sourcePivot < gap)
    (ρ : ℕ) (hρ : ρ ≤ (F.modulus w : ℕ) ^ 2) (Δ : ℤ)
    (hexact : (F.modulus w : ℤ) * Δ = (alignmentIntegerNumerator q₀ w e t : ℤ) -
      (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ) :
    |(F.modulus w : ℤ) * Δ| ≤ 2 * (F.auxiliary w gap.val : ℤ) ^ 3 := by
  have hq : (alignmentIntegerNumerator q₀ w e t : ℤ) ≤ (F.auxiliary w gap.val : ℤ) ^ 2 := by
    exact_mod_cast selected_alignmentIntegerNumerator_polynomial_bound hF q₀ w gap t ht e he
  have htt : (alignmentNaturalBlockProduct t e.targetTail : ℤ) ≤ F.auxiliary w gap.val := by
    exact_mod_cast alignment_earlier_block_product_bound hF w gap t ht _ (fun j hj => (e.target_before_sourcePivot j hj).trans he)
  have hr : (ρ : ℤ) ≤ (F.auxiliary w gap.val : ℤ) ^ 2 := by
    exact_mod_cast hρ.trans (Nat.pow_le_pow_left (F.modulus_le_auxiliary w gap.val) 2)
  have htr := mul_le_mul htt hr (Int.natCast_nonneg ρ) (Int.natCast_nonneg _)
  have ha : (2 : ℤ) ≤ F.auxiliary w gap.val := by exact_mod_cast F.auxiliary_ge_two w gap.val
  rw [hexact]
  have hab : |(alignmentIntegerNumerator q₀ w e t : ℤ) -
      (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ| ≤
      |(alignmentIntegerNumerator q₀ w e t : ℤ)| + |(alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (alignmentIntegerNumerator q₀ w e t : ℤ) (-((alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ))
  have hq0 : (0 : ℤ) ≤ alignmentIntegerNumerator q₀ w e t := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  rw [abs_of_nonneg hq0, abs_of_nonneg hp0] at hab
  nlinarith [sq_nonneg (F.auxiliary w gap.val : ℤ)]


theorem selected_alignmentPairProgression_scale_small
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ : ℕ) (hq : 0 < q₀) (i gap : Fin n) (T : Finset (Fin n))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j, Nat.Coprime (x j) (primorial w)) →
      (∀ j, j < gap → x j ≤ F.cutoff w j.val ^ 2) →
      ∀ e : AlignmentAddingPair n i, e.sourcePivot < gap →
        |(alignmentPairProgression q₀ w (F.modulus w) e x : ℝ)| ≤ eps * alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x := by
  filter_upwards [eventually_ge_atTop (q₀ + 1),
    master_microcell_eventually_polynomial_small hF (fun _ => gap) 3 2 heps]
    with w hw hg x hx hcut e he
  have hd := alignmentPairResidue_master_data hF hq hw x hx e
  have hb := selected_alignmentProgressionShift_polynomial_bound hF q₀ w gap x hcut e he
    (alignmentPairResidue q₀ w (F.modulus w) e x) hd.2.1.le
    (alignmentPairProgression q₀ w (F.modulus w) e x)
    (alignmentPairProgression_exact hF hq hw x hx e)
  have hbR : |(F.modulus w : ℝ) * (alignmentPairProgression q₀ w (F.modulus w) e x : ℝ)| ≤
      2 * (F.auxiliary w gap.val : ℝ) ^ 3 := by exact_mod_cast hb
  have hM : (0 : ℝ) < F.modulus w := by exact_mod_cast (F.modulus w).pos
  rw [abs_mul, abs_of_pos hM] at hbR
  have ha : (1 : ℝ) ≤ (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by
    have hp : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by positivity
    exact_mod_cast hp
  have hR : (0 : ℝ) ≤ alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w) := by positivity
  rw [alignmentGeometryWithGap_cubeScale]
  unfold alignmentCubeScale alignmentShortBinVolume
  rw [Nat.cast_mul, ← mul_div_assoc]
  apply (le_div_iff₀ hM).mpr
  have hh := mul_le_mul_of_nonneg_right ha hR
  have hh' := mul_le_mul_of_nonneg_left hh heps.le
  nlinarith


end Hindman168
