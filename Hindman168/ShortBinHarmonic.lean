import Hindman168.ResidueHarmonic

/-!
# Uniform pivot likelihood in a multiplicative short bin

For a fixed bin `[Q,Q+W)`, its preimage under multiplication by `t`
has harmonic residue mass with a main term independent of `t`.
The estimates are finite inequalities; cutoff containment and the
probability of discarded bins are not asserted here.
-/

namespace Hindman168

theorem shortBin_log_lower {Q W : ℝ} (hQ : 0 < Q) (hW : 0 < W) :
    W / (Q + W) ≤ Real.log ((Q + W) / Q) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos (by positivity) hQ :
    0 < (Q + W) / Q)
  have he : 1 - ((Q + W) / Q)⁻¹ = W / (Q + W) := by
    field_simp
    ring
  rwa [he] at h

theorem shortBin_log_pos {Q W : ℝ} (hQ : 0 < Q) (hW : 0 < W) :
    0 < Real.log ((Q + W) / Q) := by
  exact (div_pos hW (by positivity)).trans_le (shortBin_log_lower hQ hW)

theorem shortBin_harmonic_error {Q W t : ℝ} {q a : ℕ}
    (hQ : 0 < Q) (hW : 0 < W) (ht : 0 < t) (hq : 0 < q) (ha : a < q) :
    |residueHarmonic (Q / t) ((Q + W) / t) q a -
      Real.log ((Q + W) / Q) / q| ≤ t / Q := by
  have h := residue_harmonic_error (div_pos hQ ht)
    ((div_lt_div_iff_of_pos_right ht).mpr (by linarith : Q < Q + W)) hq ha
  have he : ((Q + W) / t) / (Q / t) = (Q + W) / Q := by
    field_simp
  simpa only [he, inv_div] using h

theorem shortBin_harmonic_relative_error {Q W t : ℝ} {q a : ℕ}
    (hQ : 0 < Q) (hW : 0 < W) (hWQ : W ≤ Q) (ht : 0 < t)
    (hq : 0 < q) (ha : a < q) :
    |residueHarmonic (Q / t) ((Q + W) / t) q a -
      Real.log ((Q + W) / Q) / q| ≤
      (2 * q * t / W) * (Real.log ((Q + W) / Q) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl := shortBin_log_lower hQ hW
  have hlog : W / (2 * Q) ≤ Real.log ((Q + W) / Q) := by
    apply le_trans _ hl
    exact div_le_div_of_nonneg_left hW.le (by positivity) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * t / W)
  have he : (2 * t / W) * (W / (2 * Q)) = t / Q := by field_simp
  have he' : (2 * t / W) * Real.log ((Q + W) / Q) =
      (2 * q * t / W) * (Real.log ((Q + W) / Q) / q) := by field_simp
  rw [he, he'] at hmul
  exact (shortBin_harmonic_error hQ hW ht hq ha).trans hmul

theorem shortBin_harmonic_uniform_error {Q t tlo R C : ℝ} {q a : ℕ}
    (hQ : 0 < Q) (htlo : 0 < tlo) (hR : 0 < R) (hWQ : tlo * R ≤ Q)
    (ht : 0 < t) (htC : t ≤ C * tlo) (hq : 0 < q) (ha : a < q) :
    |residueHarmonic (Q / t) ((Q + tlo * R) / t) q a -
      Real.log ((Q + tlo * R) / Q) / q| ≤
      (2 * C * q / R) * (Real.log ((Q + tlo * R) / Q) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (shortBin_harmonic_relative_error hQ (mul_pos htlo hR) hWQ ht hq ha).trans
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (shortBin_log_pos hQ (mul_pos htlo hR)).le hqR.le)
  apply (div_le_iff₀ (mul_pos htlo hR)).mpr
  have he : (2 * C * q / R) * (tlo * R) = 2 * q * (C * tlo) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left htC (by positivity)

theorem shortBin_harmonic_half_bounds {Q t tlo R C : ℝ} {q a : ℕ}
    (hQ : 0 < Q) (htlo : 0 < tlo) (hR : 0 < R) (hWQ : tlo * R ≤ Q)
    (ht : 0 < t) (htC : t ≤ C * tlo) (hq : 0 < q) (ha : a < q)
    (hsmall : 2 * C * q / R ≤ 1 / 2) :
    (Real.log ((Q + tlo * R) / Q) / q) / 2 ≤
      residueHarmonic (Q / t) ((Q + tlo * R) / t) q a ∧
    residueHarmonic (Q / t) ((Q + tlo * R) / t) q a ≤
      3 * (Real.log ((Q + tlo * R) / Q) / q) / 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hm := div_pos (shortBin_log_pos hQ (mul_pos htlo hR)) hqR
  have he := shortBin_harmonic_uniform_error hQ htlo hR hWQ ht htC hq ha
  have hb := he.trans (mul_le_mul_of_nonneg_right hsmall hm.le)
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor <;> linarith

theorem shortBin_harmonic_comparison {Q t t' tlo R C : ℝ} {q a : ℕ}
    (hQ : 0 < Q) (htlo : 0 < tlo) (hR : 0 < R) (hWQ : tlo * R ≤ Q)
    (ht : 0 < t) (htC : t ≤ C * tlo) (ht' : 0 < t') (htC' : t' ≤ C * tlo)
    (hq : 0 < q) (ha : a < q) (hsmall : 2 * C * q / R ≤ 1 / 2) :
    residueHarmonic (Q / t) ((Q + tlo * R) / t) q a ≤
      3 * residueHarmonic (Q / t') ((Q + tlo * R) / t') q a := by
  have h := shortBin_harmonic_half_bounds hQ htlo hR hWQ ht htC hq ha hsmall
  have h' := shortBin_harmonic_half_bounds hQ htlo hR hWQ ht' htC' hq ha hsmall
  linarith [h.2, h'.1]

end Hindman168
