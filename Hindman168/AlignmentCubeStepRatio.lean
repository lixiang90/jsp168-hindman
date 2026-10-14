import Hindman168.AlignmentCubeSideLengths
import Hindman168.AlignmentResidueEndpoints

namespace Hindman168
open Filter
open scoped Topology BigOperators

theorem alignment_step_scale_small (M t a R C d eps : ℝ)
    (hM : 0 < M) (ha : 0 ≤ a) (hd : 0 ≤ d) (htC : t ≤ C * a)
    (hsmall : d * C * M ≤ eps * R) :
    d * t ≤ eps * (a * R / M) := by
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hM).mpr
  have h₁ := mul_le_mul_of_nonneg_left htC (mul_nonneg hd hM.le)
  have h₂ := mul_le_mul_of_nonneg_left hsmall ha
  nlinarith [h₁, h₂]

theorem alignment_actual_step_eventually_small
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) →
      (d : ℝ) * alignmentNaturalBlockProduct x T ≤ eps * alignmentCubeScale F w i T x := by
  have hh := master_microcell_eventually_polynomial_small hF (fun _ => i) 1
    ((d : ℝ) * (2 : ℝ) ^ T.card) heps
  filter_upwards [hh] with w hw x hx
  have hM : (F.modulus w : ℝ) ≤ F.auxiliary w i.val := by
    exact_mod_cast F.modulus_le_auxiliary w i.val
  have hsmall : (d : ℝ) * (2 : ℝ) ^ T.card * (F.modulus w : ℝ) ≤
      eps * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hM
      (by positivity : 0 ≤ (d : ℝ) * (2 : ℝ) ^ T.card)
    simp only [pow_one] at hw
    exact h.trans hw
  have ht := (binaryDyadicProduct_bounds T x hx).2
  have h := alignment_step_scale_small (F.modulus w) (alignmentNaturalBlockProduct x T)
    (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ)
    (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) ((2 : ℝ) ^ T.card) d eps
    (by exact_mod_cast (F.modulus w).pos) (by positivity) (by positivity)
    (by exact_mod_cast ht) hsmall
  simpa only [alignmentCubeScale, alignmentShortBinVolume, Nat.cast_mul] using h

theorem alignment_actual_endpoint_eventually_small
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L r b : ℤ,
      |((b + (alignmentNaturalBlockProduct x T : ℤ) * alignmentResidueEndpoint L d r) -
        (b + (alignmentNaturalBlockProduct x T : ℤ) * L) : ℤ)| ≤
          eps * alignmentCubeScale F w i T x := by
  filter_upwards [alignment_actual_step_eventually_small hF i T d heps] with w hw x hx L r b
  have ht : 0 < alignmentNaturalBlockProduct x T := by
    unfold alignmentNaturalBlockProduct
    exact Finset.prod_pos (fun j hj => hx j hj)
  have hb := alignmentResidueEndpoint_affine_displacement L d r
    (alignmentNaturalBlockProduct x T) b (by exact_mod_cast hd) (by exact_mod_cast ht)
  have he : |((b + (alignmentNaturalBlockProduct x T : ℤ) * alignmentResidueEndpoint L d r) -
        (b + (alignmentNaturalBlockProduct x T : ℤ) * L) : ℤ)| ≤
      (d : ℝ) * alignmentNaturalBlockProduct x T := by
    rw [abs_of_nonneg hb.1]
    have h := hb.2.le
    have hc : (((b + (alignmentNaturalBlockProduct x T : ℤ) * alignmentResidueEndpoint L d r) -
        (b + (alignmentNaturalBlockProduct x T : ℤ) * L) : ℤ) : ℝ) ≤
        (alignmentNaturalBlockProduct x T : ℝ) * d := by exact_mod_cast h
    simpa only [mul_comm] using hc
  exact he.trans (hw x hx)

end Hindman168
